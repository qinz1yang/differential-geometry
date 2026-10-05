import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.PiL2
import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenDiskBundle

/-!
# A smooth orthonormal frame trivializes a Riemannian vector bundle isometrically (LFR51)

Frozen blueprint master207A, lemma `lem:collapse-oriented-finite-soul-types` (LFR51, lines
29309–29378): the trivial rows of (LFR51.1) are "smooth bundle identifications … after matching the
fiber norms". Foundations review §1.2: the trivializations must be the actual norm-preserving ones.

* `exists_normPreserving_trivialization_of_orthonormal`: `k` smooth sections that are orthonormal
  in every fibre of a smooth Riemannian vector bundle with `k`-dimensional model fibre give a smooth
  diffeomorphism `B × ℝᵏ → V`, `(b, x) ↦ Σ xᵢ sᵢ(b)`, which is a linear isometry on every fibre.
* `exists_normPreserving_trivialization_of_subsingleton`: over a one-point (or empty) base every
  smooth Riemannian vector bundle is isometrically trivial (the point row `{*} | ℝ³ | D³`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Topology Manifold InnerProductSpace

namespace DifferentialGeometry.Topology.VectorBundle

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V]

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V] in
/-- Every fibre has the dimension of the model fibre. -/
theorem finrank_fiber_eq (b : B) : Module.finrank ℝ (V b) = Module.finrank ℝ F :=
  ((trivializationAt F V b).continuousLinearEquivAt ℝ b
    (FiberBundle.mem_baseSet_trivializationAt' b)).toLinearEquiv.finrank_eq

omit [ContMDiffVectorBundle ∞ F V IB] [IsContMDiffRiemannianBundle IB ∞ F V] in
/-- An orthonormal family of `finrank F` vectors in a fibre is an orthonormal basis: every vector
is the sum of its coefficients. -/
theorem sum_inner_smul_eq_of_orthonormal {k : ℕ} (hk : Module.finrank ℝ F = k) {b : B}
    {s : Fin k → V b} (hon : Orthonormal ℝ s) (v : V b) :
    ∑ i, ⟪s i, v⟫_ℝ • s i = v := by
  have : FiniteDimensional ℝ (V b) :=
    ((trivializationAt F V b).continuousLinearEquivAt ℝ b
      (FiberBundle.mem_baseSet_trivializationAt' b)).toLinearEquiv.symm.finiteDimensional
  have hsp : Submodule.span ℝ (Set.range s) = ⊤ :=
    hon.linearIndependent.span_eq_top_of_card_eq_finrank'
      (by rw [Fintype.card_fin, finrank_fiber_eq (F := F) (V := V) b, hk])
  let ob := OrthonormalBasis.mk hon hsp.ge
  have h := ob.sum_repr' v
  simpa [ob, OrthonormalBasis.coe_mk] using h

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V] in
/-- Linear combinations of smooth sections with smooth coefficients along a smooth base map are
smooth. -/
theorem contMDiff_sum_smul_along {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {k : ℕ} {β : M → B}
    (hβ : ContMDiff IM IB ∞ β) (σ : Fin k → (x : M) → V (β x))
    (hσ : ∀ i, ContMDiff IM (IB.prod 𝓘(ℝ, F)) ∞ (fun x => (⟨β x, σ i x⟩ : TotalSpace F V)))
    (c : Fin k → M → ℝ) (hc : ∀ i, ContMDiff IM 𝓘(ℝ, ℝ) ∞ (c i)) :
    ContMDiff IM (IB.prod 𝓘(ℝ, F)) ∞
      (fun x => (⟨β x, ∑ i, c i x • σ i x⟩ : TotalSpace F V)) := by
  intro x₀
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨hβ x₀, ?_⟩
  let e := trivializationAt F V (β x₀)
  have hcoord : ∀ i, ContMDiffAt IM 𝓘(ℝ, F) ∞
      (fun x => (e (⟨β x, σ i x⟩ : TotalSpace F V)).2) x₀ :=
    fun i => (Bundle.contMDiffAt_totalSpace.mp (hσ i x₀)).2
  have hsum : ContMDiffAt IM 𝓘(ℝ, F) ∞
      (fun x => ∑ i, c i x • (e (⟨β x, σ i x⟩ : TotalSpace F V)).2) x₀ :=
    contMDiffAt_finsetSum fun i _ => (hc i x₀).smul (hcoord i)
  refine hsum.congr_of_eventuallyEq ?_
  have hb : ∀ᶠ x in 𝓝 x₀, β x ∈ e.baseSet :=
    (hβ x₀).continuousAt (e.open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (β x₀)))
  filter_upwards [hb] with x hx
  have hlin := e.linear ℝ hx
  let L : V (β x) →ₗ[ℝ] F :=
    { toFun := fun v => (e (⟨β x, v⟩ : TotalSpace F V)).2
      map_add' := hlin.map_add
      map_smul' := hlin.map_smul }
  change L (∑ i, c i x • σ i x) = ∑ i, c i x • L (σ i x)
  rw [map_sum]
  simp only [map_smul]

omit [ContMDiffVectorBundle ∞ F V IB] in
/-- **LFR51, isometric trivialization from an orthonormal frame.** `k` smooth sections, orthonormal
in every fibre of a smooth Riemannian bundle with `k`-dimensional model fibre, give a smooth
diffeomorphism from the trivial bundle `B × ℝᵏ` onto the bundle, `(b, x) ↦ Σ xᵢ sᵢ(b)`; it preserves
the fibre norms. -/
theorem exists_normPreserving_trivialization_of_orthonormal {k : ℕ}
    (hk : Module.finrank ℝ F = k) (s : Fin k → (b : B) → V b)
    (hs : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) ∞ (fun b => (⟨b, s i b⟩ : TotalSpace F V)))
    (hon : ∀ b, Orthonormal ℝ (fun i => s i b)) :
    ∃ Φ : Diffeomorph (IB.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (IB.prod 𝓘(ℝ, F))
        (TotalSpace (EuclideanSpace ℝ (Fin k)) (Trivial B (EuclideanSpace ℝ (Fin k))))
        (TotalSpace F V) ∞,
      (∀ (b : B) (x : EuclideanSpace ℝ (Fin k)),
        Φ ⟨b, x⟩ = (⟨b, ∑ i, x i • s i b⟩ : TotalSpace F V)) ∧
      ∀ z, ‖(Φ z).2‖ = ‖z.2‖ := by
  let Ek := EuclideanSpace ℝ (Fin k)
  let fwd : TotalSpace Ek (Trivial B Ek) → TotalSpace F V :=
    fun z => ⟨z.proj, ∑ i, (z.2 : Ek) i • s i z.proj⟩
  let bwd : TotalSpace F V → TotalSpace Ek (Trivial B Ek) :=
    fun z => ⟨z.proj, (EuclideanSpace.equiv (Fin k) ℝ).symm (fun i => ⟪s i z.proj, z.2⟫_ℝ)⟩
  have hsnd : ContMDiff (IB.prod 𝓘(ℝ, Ek)) 𝓘(ℝ, Ek) ∞
      (fun z : TotalSpace Ek (Trivial B Ek) => (z.2 : Ek)) :=
    fun z₀ => ((Bundle.contMDiffAt_totalSpace (f := id) (x₀ := z₀) (IB := IB) (n := ∞)).mp
      contMDiffAt_id).2
  have hfwd : ContMDiff (IB.prod 𝓘(ℝ, Ek)) (IB.prod 𝓘(ℝ, F)) ∞ fwd := by
    refine contMDiff_sum_smul_along (Bundle.contMDiff_proj _)
      (fun i (z : TotalSpace Ek (Trivial B Ek)) => s i z.proj)
      (fun i => (hs i).comp (Bundle.contMDiff_proj _)) (fun i z => (z.2 : Ek) i) (fun i => ?_)
    exact ((EuclideanSpace.proj i : Ek →L[ℝ] ℝ).contMDiff).comp hsnd
  have hbwd : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, Ek)) ∞ bwd := by
    intro z₀
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨(Bundle.contMDiff_proj _) z₀, ?_⟩
    have hcoef : ContMDiffAt (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, Fin k → ℝ) ∞
        (fun z : TotalSpace F V => fun i => ⟪s i z.proj, z.2⟫_ℝ) z₀ := by
      refine contMDiffAt_pi_space.mpr fun i => ?_
      exact ContMDiffAt.inner_bundle (b := fun z : TotalSpace F V => z.proj)
        (v := fun z => s i z.proj) (w := fun z => z.2)
        ((hs i).comp (Bundle.contMDiff_proj _) z₀) contMDiffAt_id
    exact ((((EuclideanSpace.equiv (Fin k) ℝ).symm : (Fin k → ℝ) →L[ℝ] Ek).contMDiff).contMDiffAt).comp
      z₀ hcoef
  have hleft : Function.LeftInverse bwd fwd := by
    intro z
    change (⟨z.proj, (EuclideanSpace.equiv (Fin k) ℝ).symm
      (fun i => ⟪s i z.proj, ∑ j, (z.2 : Ek) j • s j z.proj⟫_ℝ)⟩ :
        TotalSpace Ek (Trivial B Ek)) = z
    have hc : (fun i => ⟪s i z.proj, ∑ j, (z.2 : Ek) j • s j z.proj⟫_ℝ) =
        fun i => (z.2 : Ek) i := by
      funext i
      exact (hon z.proj).inner_right_fintype (fun j => (z.2 : Ek) j) i
    rw [hc]
    rfl
  have hright : Function.RightInverse bwd fwd := by
    intro z
    change (⟨z.proj, ∑ i, ((EuclideanSpace.equiv (Fin k) ℝ).symm
      (fun i => ⟪s i z.proj, z.2⟫_ℝ) : Ek) i • s i z.proj⟩ : TotalSpace F V) = z
    have h := sum_inner_smul_eq_of_orthonormal (F := F) hk (hon z.proj) z.2
    simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply] at *
    rw [show (∑ i, (WithLp.toLp 2 (fun i => ⟪s i z.proj, z.2⟫_ℝ) : Ek) i • s i z.proj) =
      ∑ i, ⟪s i z.proj, z.2⟫_ℝ • s i z.proj from rfl, h]
  let Φ : Diffeomorph (IB.prod 𝓘(ℝ, Ek)) (IB.prod 𝓘(ℝ, F)) (TotalSpace Ek (Trivial B Ek))
      (TotalSpace F V) ∞ :=
    { toFun := fwd
      invFun := bwd
      left_inv := hleft
      right_inv := hright
      contMDiff_toFun := hfwd
      contMDiff_invFun := hbwd }
  refine ⟨Φ, fun b x => rfl, fun z => ?_⟩
  change ‖∑ i, (z.2 : Ek) i • s i z.proj‖ = ‖(z.2 : Ek)‖
  have hsq : ‖∑ i, (z.2 : Ek) i • s i z.proj‖ ^ 2 = ‖(z.2 : Ek)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, (hon z.proj).inner_sum, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

omit [ContMDiffVectorBundle ∞ F V IB] in
/-- **LFR51, the point row.** Over a base with at most one point every smooth Riemannian vector
bundle with `k`-dimensional model fibre is isometrically and smoothly trivial. -/
theorem exists_normPreserving_trivialization_of_subsingleton [Subsingleton B] {k : ℕ}
    (hk : Module.finrank ℝ F = k) :
    ∃ Φ : Diffeomorph (IB.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (IB.prod 𝓘(ℝ, F))
        (TotalSpace (EuclideanSpace ℝ (Fin k)) (Trivial B (EuclideanSpace ℝ (Fin k))))
        (TotalSpace F V) ∞,
      (∀ z, (Φ z).proj = z.proj) ∧ ∀ z, ‖(Φ z).2‖ = ‖z.2‖ := by
  rcases isEmpty_or_nonempty B with hB | ⟨⟨b₀⟩⟩
  · obtain ⟨Φ, -, hn⟩ := exists_normPreserving_trivialization_of_orthonormal (IB := IB) (V := V) hk
      (fun _ (b : B) => (IsEmpty.false b).elim) (fun _ (b : B) => (IsEmpty.false b).elim)
      (fun (b : B) => (IsEmpty.false b).elim)
    exact ⟨Φ, fun z => (IsEmpty.false z.proj).elim, hn⟩
  · have : FiniteDimensional ℝ (V b₀) :=
      ((trivializationAt F V b₀).continuousLinearEquivAt ℝ b₀
        (FiberBundle.mem_baseSet_trivializationAt' b₀)).toLinearEquiv.symm.finiteDimensional
    have hdim : Module.finrank ℝ (V b₀) = k := (finrank_fiber_eq (F := F) (V := V) b₀).trans hk
    let ob : OrthonormalBasis (Fin k) ℝ (V b₀) := (stdOrthonormalBasis ℝ (V b₀)).reindex
      (finCongr hdim)
    let s : Fin k → (b : B) → V b := fun i b => Subsingleton.elim b₀ b ▸ ob i
    have hconst : ∀ i, (fun b => (⟨b, s i b⟩ : TotalSpace F V)) =
        fun _ => (⟨b₀, ob i⟩ : TotalSpace F V) := by
      intro i
      funext b
      cases Subsingleton.elim b₀ b
      rfl
    have hs : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) ∞
        (fun b => (⟨b, s i b⟩ : TotalSpace F V)) := by
      intro i
      rw [hconst i]
      exact contMDiff_const
    have hon : ∀ b, Orthonormal ℝ (fun i => s i b) := by
      intro b
      cases Subsingleton.elim b₀ b
      exact ob.orthonormal
    obtain ⟨Φ, hΦ, hn⟩ := exists_normPreserving_trivialization_of_orthonormal hk s hs hon
    exact ⟨Φ, fun z => congrArg TotalSpace.proj (hΦ z.proj z.2), hn⟩

end DifferentialGeometry.Topology.VectorBundle
