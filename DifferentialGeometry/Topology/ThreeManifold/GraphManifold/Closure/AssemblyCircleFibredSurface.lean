import DifferentialGeometry.Topology.Ehresmann.CircleFibreTransport
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FibreCoordinate
import DifferentialGeometry.Topology.Manifold.ProductOrientationCongruence
import DifferentialGeometry.Topology.Manifold.OneManifold.CircleConsequences
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.AddCircle.DiffeomorphLift
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarBundleMobiusTwist

/-!
# Chapter-14 assembly, bridge B2-param: circle-fibred surfaces over a circle are tori

`exists_torus_param_of_circle_fibred_surface` (frozen B2-param, V3: the redundant
`[ConnectedSpace S]` of V1/V2 is dropped, see its docstring) gives an actual torus parametrization
`e : T² ≃ S` with `p ∘ e = fst` for an oriented compact surface fibred over the circle with
connected fibres (design `docs/geometrization/chapter14/design-fc39-fc42-assembly-20261004.md`, §3
"B2-param", §7 R7). It reuses ASM-L3's cut along one fibre
(`DG/Topology/Ehresmann/CircleFibreTransport.lean`, `exists_circleCut`).

* Orientation (`false_of_neg_monodromy_lift`): if the monodromy lift were decreasing, the deck map
  `T = φ × (s ↦ s - 1)` of the cut would preserve the pulled-back orientation, hence the product
  orientation (connectedness, `preservesOrientation_or_opposite`), while reversing it because `φ`
  has derivative `-F' < 0` at a fixed point (`exists_fixed_mfderiv_neg`).
* Isotopy (`lineInterp`, `circleInterp`): `(1 - χ θ) x + χ θ G x` with `G` the increasing lift of
  `φ⁻¹` and `χ = stepThirds` flat outside `[1/3, 2/3]`; the derivative stays positive.
* Torus map (`exists_torus_param_of_positive_cut`): `e₀ (y, z) = Ψ (hθ z, θ)` with
  `θ = angleLift 0 y`; smooth across the cut by the periodicity on `[-1/3, 1/3]`; a bijective local
  diffeomorphism, hence a diffeomorphism.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section Pullback

variable {E H M F K N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ F K} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

/-- A deck-type diffeomorphism (`f ∘ T = f`) preserves the orientation pulled back along `f`. -/
theorem preservesOrientation_pullback_of_comp_eq {n : ℕ} (hn : Module.finrank ℝ E = n)
    (f : M → N) (hf : ContMDiff I J ∞ f) (hbij : ∀ x, Bijective (mfderiv I J f x))
    (O : ManifoldOrientation J N n) (T : M ≃ₘ⟮I, I⟯ M) (hT : ∀ x, f (T x) = f x) :
    T.preservesOrientation
      (DifferentialGeometry.Topology.Manifold.manifoldOrientationPullback I J hn f hf hbij O)
      (DifferentialGeometry.Topology.Manifold.manifoldOrientationPullback I J hn f hf hbij O) := by
  intro x
  set o := DifferentialGeometry.Topology.Manifold.manifoldOrientationPullback I J hn f hf hbij O
  let Dx : E ≃ₗ[ℝ] F := (DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective I J f
    hbij x).toLinearEquiv
  let DT : E ≃ₗ[ℝ] F := (DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective I J f
    hbij (T x)).toLinearEquiv
  let dT : E ≃ₗ[ℝ] E := (T.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  have h1 : Orientation.map (Fin n) Dx (o.orientation x) = O.orientation (f x) :=
    DifferentialGeometry.Topology.Manifold.orientation_map_manifoldOrientationPullback
      I J hn f hf hbij O x
  have h2 : Orientation.map (Fin n) DT (o.orientation (T x)) = O.orientation (f (T x)) :=
    DifferentialGeometry.Topology.Manifold.orientation_map_manifoldOrientationPullback
      I J hn f hf hbij O (T x)
  have hchain : dT.trans DT = Dx := by
    apply LinearEquiv.ext
    intro v
    have hc := mfderiv_comp_apply (I' := I) x (hf.mdifferentiableAt (by simp) (x := T x))
      (T.mdifferentiable (by simp) x) v
    have hfT : f ∘ T = f := funext hT
    change mfderiv I J f (T x) (mfderiv I I T x v) = mfderiv I J f x v
    rw [← hc, hfT]
  have hmapeq : Orientation.map (Fin n) DT (Orientation.map (Fin n) dT (o.orientation x)) =
      Orientation.map (Fin n) DT (o.orientation (T x)) := by
    have e1 := orientation_map_trans_fin dT DT (o.orientation x)
    rw [hchain] at e1
    have e2 : (O.orientation (f x) : Orientation ℝ F (Fin n)) = O.orientation (f (T x)) := by
      rw [hT x]
    exact e1.symm.trans (h1.trans (e2.trans h2.symm))
  exact (Orientation.map (Fin n) DT).injective hmapeq

end Pullback

section Fibre

/-- **The fibre over `1` as an actual circle.** For a submersion of a compact surface onto the
circle with connected fibre over `1`, that fibre is the range of a smooth embedding of the circle
`AddCircle 1`. -/
theorem exists_addCircle_fibre_embedding {S : Type u} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S] [CompactSpace S]
    [T2Space S] (p : S → Circle) (hp : ContMDiff (𝓡 2) (𝓡 1) ∞ p)
    (hsub : ∀ x, Surjective (mfderiv (𝓡 2) (𝓡 1) p x)) (hconn : IsConnected (p ⁻¹' {1})) :
    ∃ f : AddCircle (1 : ℝ) → S, IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ f ∧ range f = p ⁻¹' {1} := by
  let _ := DifferentialGeometry.Topology.Manifold.regularFiberChartedSpace p 1 hp
    (fun x _ => hsub x)
  have hman := DifferentialGeometry.Topology.Manifold.regularFiberIsManifold p 1 hp
    (fun x _ => hsub x)
  obtain ⟨c⟩ :=
    DifferentialGeometry.Topology.Manifold.OneManifold.nonempty_circle_diffeomorph_regularFiber
      p 1 hp (fun x _ => hsub x) (by simp)
      (isClosed_singleton.preimage hp.continuous).isCompact hconn
  let dC := AddCircle.diffeomorphCircle
  let f : AddCircle (1 : ℝ) → S := fun t => (c (dC t)).val
  have hval := DifferentialGeometry.Topology.Manifold.contMDiff_regularFiberInclusion p 1 hp
    (fun x _ => hsub x)
  have hf : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ f := (hval.comp c.contMDiff).comp dC.contMDiff
  have hinj : ∀ t, Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) f t) := by
    intro t
    have h1 := DifferentialGeometry.Topology.Manifold.mfderiv_regularFiberInclusion_injective
      p 1 hp (fun x _ => hsub x) (c (dC t))
    have hc1 : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) f t =
        (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) -
            Module.finrank ℝ (EuclideanSpace ℝ (Fin 1))) → ℝ) (𝓡 2) Subtype.val (c (dC t))).comp
          ((mfderiv (𝓡 1) 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) -
            Module.finrank ℝ (EuclideanSpace ℝ (Fin 1))) → ℝ) c (dC t)).comp
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) dC t)) := by
      have hcd := mfderiv_comp t ((c.contMDiff.mdifferentiable (by simp)) (dC t))
        ((dC.contMDiff.mdifferentiable (by simp)) t)
      have hvc := mfderiv_comp t ((hval.mdifferentiable (by simp)) (c (dC t)))
        (((c.contMDiff.comp dC.contMDiff).mdifferentiable (by simp)) t)
      rw [← hcd]
      exact hvc
    rw [hc1, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
    exact h1.comp ((c.mfderivToContinuousLinearEquiv (by simp) (dC t)).injective.comp
      (dC.mfderivToContinuousLinearEquiv (by simp) t).injective)
  refine ⟨f, ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp)
    hf hinj, Topology.IsEmbedding.subtypeVal.comp (c.toHomeomorph.isEmbedding.comp
      dC.toHomeomorph.isEmbedding)⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact (c (dC t)).2
  · intro hx
    refine ⟨dC.symm (c.symm ⟨x, hx⟩), ?_⟩
    change (c (dC (dC.symm (c.symm ⟨x, hx⟩)))).val = x
    rw [dC.apply_symm_apply, c.apply_symm_apply]

end Fibre

section CircleOrientation

/-- An orientation of the circle `AddCircle 1` (pulled back from `circleOrientation`). -/
def addCircleOrientation : ManifoldOrientation 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) 1 :=
  DifferentialGeometry.Topology.Manifold.manifoldOrientationPullback 𝓘(ℝ, ℝ) (𝓡 1)
    (Module.finrank_self ℝ) AddCircle.diffeomorphCircle AddCircle.diffeomorphCircle.contMDiff
    (fun t => (AddCircle.diffeomorphCircle.mfderivToContinuousLinearEquiv (by simp) t).bijective)
    GC.Seifert.circleOrientation

/-- An orientation of the line (pulled back from the circle along the covering). -/
def lineOrientation : ManifoldOrientation 𝓘(ℝ, ℝ) ℝ 1 :=
  DifferentialGeometry.Topology.Manifold.manifoldOrientationPullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
    (Module.finrank_self ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) AddCircle.contMDiff_coe
    AddCircle.bijective_mfderiv_coe addCircleOrientation

/-- The unit translation of the line. -/
def lineShift : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ where
  toEquiv := Equiv.subRight 1
  contMDiff_toFun := (contDiff_id.sub contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff

theorem lineShift_preservesOrientation :
    lineShift.preservesOrientation lineOrientation lineOrientation :=
  preservesOrientation_pullback_of_comp_eq (Module.finrank_self ℝ)
    (fun t : ℝ => (t : AddCircle (1 : ℝ))) AddCircle.contMDiff_coe
    AddCircle.bijective_mfderiv_coe addCircleOrientation lineShift (fun t => by
      change ((t - 1 : ℝ) : AddCircle (1 : ℝ)) = t
      rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero])

end CircleOrientation

section Monodromy

/-- The derivative of the covering `ℝ → AddCircle 1` depends only on the image point. -/
theorem mfderiv_coe_eq_of_coe_eq {x y : ℝ} (h : (x : AddCircle (1 : ℝ)) = y) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) x =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) y := by
  have heq : (fun t : ℝ => ((t + (y - x) : ℝ) : AddCircle (1 : ℝ))) =
      fun t : ℝ => (t : AddCircle (1 : ℝ)) := by
    funext t
    simp only [AddCircle.coe_add, AddCircle.coe_sub, ← h, sub_self, add_zero]
  have hder : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + (y - x)) x =
      ContinuousLinearMap.id ℝ ℝ := by
    rw [mfderiv_eq_fderiv]
    exact (hasFDerivAt_id x |>.add_const (y - x)).fderiv
  have hh := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
    (f := fun t : ℝ => t + (y - x))
    (g := fun t : ℝ => (t : AddCircle (1 : ℝ))) x
    (AddCircle.contMDiff_coe.mdifferentiableAt (by decide))
    ((contDiff_id.add contDiff_const :
      ContDiff ℝ ∞ (fun t : ℝ => t + (y - x))).contMDiff.mdifferentiableAt (by decide))
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => ((t + (y - x) : ℝ) : AddCircle (1 : ℝ))) x =
    _ at hh
  rw [heq] at hh
  have hcomp' : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) x =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) (x + (y - x)) := by
    rw [hder] at hh
    apply ContinuousLinearMap.coeFn_injective
    funext z
    exact congrFun (congrArg DFunLike.coe hh) z
  rw [show x + (y - x) = y by ring] at hcomp'
  exact hcomp'

/-- A circle diffeomorphism with a decreasing lift (`φ t = -(F t)`, `F` increasing of degree
one) has a fixed point, at which its derivative is multiplication by `-F' < 0`. -/
theorem exists_fixed_mfderiv_neg (φ : AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ AddCircle (1 : ℝ))
    (F : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ) (hF1 : ∀ t, F (t + 1) = F t + 1)
    (hneg : ∀ t : ℝ, φ (t : AddCircle (1 : ℝ)) = -(F t : AddCircle (1 : ℝ))) :
    ∃ t₀ : ℝ, φ (t₀ : AddCircle (1 : ℝ)) = t₀ ∧
      ∀ v, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ (t₀ : AddCircle (1 : ℝ)) v = (-deriv F t₀) • v := by
  have hFn : ∀ (n : ℕ) (t : ℝ), F (t + n) = F t + n := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      rw [Nat.cast_succ, ← add_assoc, hF1, ih]
      ring
  have hFc : Continuous F := F.continuous
  let G : ℝ → ℝ := fun t => F t + t
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |F 0| ≤ N := ⟨⌈|F 0|⌉₊, Nat.le_ceil _⟩
  have hGN : 0 ≤ G N := by
    have := hFn N 0
    simp only [zero_add] at this
    simp only [G, this]
    have := neg_abs_le (F 0)
    linarith
  have hGmN : G (-N) ≤ 0 := by
    have h := hFn N (-N)
    simp only [neg_add_cancel] at h
    simp only [G]
    have := le_abs_self (F 0)
    linarith
  obtain ⟨t₀, -, ht₀⟩ := intermediate_value_Icc (show (-N : ℝ) ≤ N by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith) ((hFc.add continuous_id).continuousOn) ⟨hGmN, hGN⟩
  have hfix : φ (t₀ : AddCircle (1 : ℝ)) = t₀ := by
    rw [hneg, ← AddCircle.coe_neg]
    congr 1
    change F t₀ + t₀ = 0 at ht₀
    linarith
  refine ⟨t₀, hfix, ?_⟩
  have hcomp : (φ ∘ fun t : ℝ => (t : AddCircle (1 : ℝ))) =
      (fun t : ℝ => (t : AddCircle (1 : ℝ))) ∘ fun t => -F t := by
    funext t
    simp only [Function.comp_apply, hneg, AddCircle.coe_neg]
  have hdF : HasFDerivAt (fun t => -F t)
      (-(ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv F t₀))) t₀ :=
    ((F.contMDiff.contDiff.differentiable (by simp) t₀).hasDerivAt.hasFDerivAt).neg
  have hcoe := mfderiv_coe_eq_of_coe_eq (x := -F t₀) (y := t₀) (by
    rw [AddCircle.coe_neg, ← hneg, hfix])
  let D := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) t₀
  have hL := mfderiv_comp (I' := 𝓘(ℝ, ℝ)) t₀ ((φ.contMDiff.mdifferentiable (by simp)) _)
    ((AddCircle.contMDiff_coe.mdifferentiable (by simp)) t₀)
  have hR := mfderiv_comp (I' := 𝓘(ℝ, ℝ)) t₀
    ((AddCircle.contMDiff_coe.mdifferentiable (by simp)) (-F t₀))
    (hdF.differentiableAt.mdifferentiableAt)
  rw [hcomp, hR, hcoe, hdF.hasMFDerivAt.mfderiv] at hL
  intro v
  obtain ⟨u, rfl⟩ := (AddCircle.bijective_mfderiv_coe t₀).2 v
  have hu := congrArg (fun L => L u) hL
  change D (-((show ℝ from u) * deriv F t₀)) =
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ (t₀ : AddCircle (1 : ℝ)) (D u) at hu
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ (t₀ : AddCircle (1 : ℝ)) (D u) = (-deriv F t₀) • D u
  rw [← hu, show -((show ℝ from u) * deriv F t₀) = (-deriv F t₀) • (show ℝ from u) by
    rw [smul_eq_mul]; ring]
  exact D.map_smul (-deriv F t₀) u

end Monodromy

section Exclusion

/-- **Orientation excludes the Klein bottle.** If an oriented surface is the image of a local
diffeomorphism `Ψ : S¹ × ℝ → S` with `Ψ (z, s + 1) = Ψ (φ z, s)`, the monodromy `φ` cannot have a
decreasing lift. Route: the deck map `T = φ × (s ↦ s - 1)` preserves the pulled-back orientation,
hence the product orientation (connectedness), but reverses it because `φ` reverses the circle
orientation (derivative `-F' < 0` at a fixed point). -/
theorem false_of_neg_monodromy_lift {S : Type u} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    (o : ManifoldOrientation (𝓡 2) S 2) (Ψ : AddCircle (1 : ℝ) × ℝ → S)
    (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ Ψ)
    (hΨbij : ∀ q, Bijective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) Ψ q))
    (φ : AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ AddCircle (1 : ℝ))
    (hper : ∀ z s, Ψ (z, s + 1) = Ψ (φ z, s))
    (F : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ) (hF1 : ∀ t, F (t + 1) = F t + 1) (hF' : ∀ t, 0 < deriv F t)
    (hneg : ∀ t : ℝ, φ (t : AddCircle (1 : ℝ)) = -(F t : AddCircle (1 : ℝ))) : False := by
  obtain ⟨t₀, hfix, hdφ⟩ := exists_fixed_mfderiv_neg φ F hF1 hneg
  let oA := addCircleOrientation
  -- `φ` reverses the circle orientation
  have hrev : φ.preservesOrientation oA oA.opposite := by
    rcases GC.Seifert.preservesOrientation_or_opposite φ oA oA with h | h
    · exfalso
      let L : ℝ ≃ₗ[ℝ] ℝ :=
        (φ.mfderivToContinuousLinearEquiv (by simp) (t₀ : AddCircle (1 : ℝ))).toLinearEquiv
      have hLv : ∀ v, L v = (-deriv F t₀) • v := fun v => hdφ v
      have hL : (L : ℝ →ₗ[ℝ] ℝ) = (-deriv F t₀) • LinearMap.id := by
        refine LinearMap.ext fun v => ?_
        rw [LinearEquiv.coe_coe, hLv, LinearMap.smul_apply, LinearMap.id_apply]
      have hdet : LinearMap.det (L : ℝ →ₗ[ℝ] ℝ) < 0 := by
        rw [hL, LinearMap.det_smul, LinearMap.det_id, Module.finrank_self]
        have := hF' t₀
        simp only [pow_one, mul_one]
        linarith
      have hcard : Fintype.card (Fin 1) = Module.finrank ℝ ℝ := by simp
      have hneg' := (Orientation.map_eq_neg_iff_det_neg
        (oA.orientation (t₀ : AddCircle (1 : ℝ))) L hcard).mpr hdet
      have hpos : Orientation.map (Fin 1) L (oA.orientation (t₀ : AddCircle (1 : ℝ))) =
          oA.orientation (t₀ : AddCircle (1 : ℝ)) := by
        have h2 := h (t₀ : AddCircle (1 : ℝ))
        rw [hfix] at h2
        exact h2
      exact Module.Ray.ne_neg_self (oA.orientation (t₀ : AddCircle (1 : ℝ)))
        (hpos.symm.trans hneg')
    · have h' := Diffeomorph.preservesOrientation_opposite h
      rwa [ManifoldOrientation.opposite_opposite] at h'
  -- the deck map
  let T : (AddCircle (1 : ℝ) × ℝ) ≃ₘ⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯
      (AddCircle (1 : ℝ) × ℝ) := φ.prodCongr lineShift
  have hT : ∀ q, Ψ (T q) = Ψ q := by
    rintro ⟨z, s⟩
    change Ψ (φ z, s - 1) = Ψ (z, s)
    rw [← hper z (s - 1), sub_add_cancel]
  have hn2 : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  let o' := DifferentialGeometry.Topology.Manifold.manifoldOrientationPullback
    (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) hn2 Ψ hΨ hΨbij o
  have hTo' : T.preservesOrientation o' o' :=
    preservesOrientation_pullback_of_comp_eq hn2 Ψ hΨ hΨbij o T hT
  let ostd := DifferentialGeometry.productOrientation 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) le_rfl le_rfl oA
    lineOrientation
  have hTrev : T.preservesOrientation ostd ostd.opposite := by
    have h := Diffeomorph.prodCongr_preservesOrientation (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ))
      (I' := 𝓘(ℝ, ℝ)) (J' := 𝓘(ℝ, ℝ)) le_rfl le_rfl φ lineShift hrev
      lineShift_preservesOrientation
    rw [← GC.Seifert.MobiusCover.productOrientation_opposite_left] at h
    exact h
  let x₀ : AddCircle (1 : ℝ) × ℝ := (0, 0)
  have hcard : Fintype.card (Fin (1 + 1)) = Module.finrank ℝ (TangentSpace
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) x₀) := by
    change Fintype.card (Fin (1 + 1)) = Module.finrank ℝ (ℝ × ℝ)
    simp
  have hTstd : T.preservesOrientation ostd ostd := by
    rcases Orientation.eq_or_eq_neg (o'.orientation x₀) (ostd.orientation x₀) hcard with h | h
    · rw [← ManifoldOrientation.eq_of_eq_at o' ostd x₀ h]
      exact hTo'
    · have h' : o'.orientation x₀ = ostd.opposite.orientation x₀ := by
        rw [ManifoldOrientation.opposite_orientation]
        exact h
      have heq := ManifoldOrientation.eq_of_eq_at o' ostd.opposite x₀ h'
      have hT2 : T.preservesOrientation ostd.opposite ostd.opposite := heq ▸ hTo'
      have h3 := Diffeomorph.preservesOrientation_opposite hT2
      rwa [ManifoldOrientation.opposite_opposite] at h3
  have h1 := hTstd x₀
  have h2 := hTrev x₀
  rw [h1, ManifoldOrientation.opposite_orientation] at h2
  exact Module.Ray.ne_neg_self _ h2

end Exclusion

section Interpolation

/-- The smooth step: `0` on `(-∞, 1/3]`, `1` on `[2/3, ∞)`. -/
def stepThirds (θ : ℝ) : ℝ := Real.smoothTransition (3 * θ - 1)

theorem contDiff_stepThirds : ContDiff ℝ ∞ stepThirds :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem stepThirds_of_le {θ : ℝ} (h : θ ≤ 1 / 3) : stepThirds θ = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem stepThirds_of_ge {θ : ℝ} (h : 2 / 3 ≤ θ) : stepThirds θ = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem stepThirds_nonneg (θ : ℝ) : 0 ≤ stepThirds θ := Real.smoothTransition.nonneg _

theorem stepThirds_le_one (θ : ℝ) : stepThirds θ ≤ 1 := Real.smoothTransition.le_one _

/-- The convex interpolation `(1 - χ θ) x + χ θ G x` between the identity and `G`. -/
def lineInterp (G : ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  (1 - stepThirds q.1) * q.2 + stepThirds q.1 * G q.2

variable {G : ℝ → ℝ}

theorem contDiff_lineInterp (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (lineInterp G) :=
  ((contDiff_const.sub (contDiff_stepThirds.comp contDiff_fst)).mul contDiff_snd).add
    ((contDiff_stepThirds.comp contDiff_fst).mul (hG.comp contDiff_snd))

theorem lineInterp_add_one (hG1 : ∀ t, G (t + 1) = G t + 1) (θ x : ℝ) :
    lineInterp G (θ, x + 1) = lineInterp G (θ, x) + 1 := by
  simp only [lineInterp, hG1]
  ring

theorem hasDerivAt_lineInterp (hG : ContDiff ℝ ∞ G) (θ x : ℝ) :
    HasDerivAt (fun y => lineInterp G (θ, y))
      ((1 - stepThirds θ) + stepThirds θ * deriv G x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (1 - stepThirds θ) * y) (1 - stepThirds θ) x := by
    simpa using (hasDerivAt_id x).const_mul (1 - stepThirds θ)
  have h2 : HasDerivAt (fun y : ℝ => stepThirds θ * G y) (stepThirds θ * deriv G x) x :=
    ((hG.differentiable (by simp) x).hasDerivAt).const_mul _
  exact h1.add h2

theorem deriv_lineInterp_pos (hG' : ∀ t, 0 < deriv G t) (θ x : ℝ) :
    0 < (1 - stepThirds θ) + stepThirds θ * deriv G x := by
  have h0 := stepThirds_nonneg θ
  have h1 := stepThirds_le_one θ
  have h2 := hG' x
  rcases eq_or_lt_of_le h1 with h | h
  · rw [h]
    linarith
  · nlinarith

theorem strictMono_lineInterp (hG : ContDiff ℝ ∞ G) (hG' : ∀ t, 0 < deriv G t) (θ : ℝ) :
    StrictMono fun y => lineInterp G (θ, y) :=
  strictMono_of_hasDerivAt_pos (fun x => hasDerivAt_lineInterp hG θ x)
    (fun x => deriv_lineInterp_pos hG' θ x)

theorem lineInterp_add_nat (hG1 : ∀ t, G (t + 1) = G t + 1) (θ x : ℝ) (n : ℕ) :
    lineInterp G (θ, x + n) = lineInterp G (θ, x) + n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, lineInterp_add_one hG1, ih]
    ring

theorem lineInterp_add_int (hG1 : ∀ t, G (t + 1) = G t + 1) (θ x : ℝ) (k : ℤ) :
    lineInterp G (θ, x + k) = lineInterp G (θ, x) + k := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · exact_mod_cast lineInterp_add_nat hG1 θ x n
  · have h := lineInterp_add_nat hG1 θ (x + ((-(n : ℤ) : ℤ) : ℝ)) n
    push_cast at h ⊢
    rw [neg_add_cancel_right] at h
    linarith

theorem coe_int_eq_zero (k : ℤ) : ((k : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  rw [show (k : ℝ) = k • (1 : ℝ) by simp, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]

theorem surjective_lineInterp (hG : ContDiff ℝ ∞ G) (hG1 : ∀ t, G (t + 1) = G t + 1)
    (θ : ℝ) : Surjective fun y => lineInterp G (θ, y) := by
  intro u
  have hc : Continuous fun y => lineInterp G (θ, y) :=
    (contDiff_lineInterp hG).continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |u - lineInterp G (θ, 0)| ≤ N := ⟨_, Nat.le_ceil _⟩
  have hup : u ≤ lineInterp G (θ, (N : ℝ)) := by
    have := lineInterp_add_nat hG1 θ 0 N
    rw [zero_add] at this
    rw [this]
    have := le_abs_self (u - lineInterp G (θ, 0))
    linarith
  have hdown : lineInterp G (θ, -(N : ℝ)) ≤ u := by
    have := lineInterp_add_nat hG1 θ (-(N : ℝ)) N
    rw [neg_add_cancel] at this
    have h2 := neg_abs_le (u - lineInterp G (θ, 0))
    linarith
  obtain ⟨y, -, hy⟩ := intermediate_value_Icc (show -(N : ℝ) ≤ N by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith) hc.continuousOn ⟨hdown, hup⟩
  exact ⟨y, hy⟩

theorem periodic_lineInterp (hG1 : ∀ t, G (t + 1) = G t + 1) (θ : ℝ) :
    Function.Periodic (fun x => (lineInterp G (θ, x) : AddCircle (1 : ℝ))) 1 := by
  intro x
  simp only [lineInterp_add_one hG1, AddCircle.coe_add, AddCircle.coe_period, add_zero]

/-- The interpolated circle maps. -/
def circleInterp (hG1 : ∀ t, G (t + 1) = G t + 1) (θ : ℝ) :
    AddCircle (1 : ℝ) → AddCircle (1 : ℝ) :=
  (periodic_lineInterp hG1 θ).lift

theorem circleInterp_coe (hG1 : ∀ t, G (t + 1) = G t + 1) (θ x : ℝ) :
    circleInterp hG1 θ (x : AddCircle (1 : ℝ)) = (lineInterp G (θ, x) : AddCircle (1 : ℝ)) :=
  (periodic_lineInterp hG1 θ).lift_coe x

theorem contMDiff_circleInterp (hG : ContDiff ℝ ∞ G) (hG1 : ∀ t, G (t + 1) = G t + 1) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × AddCircle (1 : ℝ) => circleInterp hG1 q.1 q.2) := by
  have hlift : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × ℝ => ((lineInterp G q : ℝ) : AddCircle (1 : ℝ))) :=
    AddCircle.contMDiff_coe.comp ((contDiff_lineInterp hG).contMDiff.comp
      (contMDiff_fst.prodMk_space contMDiff_snd))
  have h := AddCircle.contMDiffOn_of_comp_coe (U := (univ : Set ℝ))
    (f := fun q : ℝ × AddCircle (1 : ℝ) => circleInterp hG1 q.1 q.2) (by
      refine hlift.contMDiffOn.congr fun q _ => ?_
      exact circleInterp_coe hG1 q.1 q.2)
  rw [univ_prod_univ] at h
  exact contMDiffOn_univ.mp h

theorem injective_circleInterp (hG : ContDiff ℝ ∞ G) (hG' : ∀ t, 0 < deriv G t)
    (hG1 : ∀ t, G (t + 1) = G t + 1) (θ : ℝ) : Injective (circleInterp hG1 θ) := by
  intro z z' h
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨x', rfl⟩ := QuotientAddGroup.mk_surjective z'
  change circleInterp hG1 θ (x : AddCircle (1 : ℝ)) = circleInterp hG1 θ (x' : AddCircle (1 : ℝ))
    at h
  rw [circleInterp_coe, circleInterp_coe, QuotientAddGroup.eq] at h
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  rw [zsmul_eq_mul, mul_one] at hk
  have hx' : lineInterp G (θ, x') = lineInterp G (θ, x + k) := by
    rw [lineInterp_add_int hG1]
    linarith
  have := (strictMono_lineInterp hG hG' θ).injective hx'
  change ((x : ℝ) : AddCircle (1 : ℝ)) = (x' : AddCircle (1 : ℝ))
  rw [this, AddCircle.coe_add, coe_int_eq_zero, add_zero]

theorem surjective_circleInterp (hG : ContDiff ℝ ∞ G) (hG1 : ∀ t, G (t + 1) = G t + 1)
    (θ : ℝ) : Surjective (circleInterp hG1 θ) := by
  intro z
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨y, hy⟩ := surjective_lineInterp hG hG1 θ u
  refine ⟨(y : AddCircle (1 : ℝ)), ?_⟩
  rw [circleInterp_coe]
  exact congrArg _ hy

theorem contMDiff_circleInterp_slice (hG : ContDiff ℝ ∞ G) (hG1 : ∀ t, G (t + 1) = G t + 1)
    (θ : ℝ) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (circleInterp hG1 θ) := by
  have hpair : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun z : AddCircle (1 : ℝ) => ((θ, z) : ℝ × AddCircle (1 : ℝ))) :=
    contMDiff_const.prodMk contMDiff_id
  have h := (contMDiff_circleInterp hG hG1).comp hpair
  exact h

theorem bijective_mfderiv_circleInterp (hG : ContDiff ℝ ∞ G) (hG' : ∀ t, 0 < deriv G t)
    (hG1 : ∀ t, G (t + 1) = G t + 1) (θ : ℝ) (z : AddCircle (1 : ℝ)) :
    Bijective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (circleInterp hG1 θ) z) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  set d := (1 - stepThirds θ) + stepThirds θ * deriv G x with hd
  have hd0 : d ≠ 0 := (deriv_lineInterp_pos hG' θ x).ne'
  have hcomp : (circleInterp hG1 θ ∘ fun t : ℝ => (t : AddCircle (1 : ℝ))) =
      (fun t : ℝ => (t : AddCircle (1 : ℝ))) ∘ fun y => lineInterp G (θ, y) :=
    funext fun y => circleInterp_coe hG1 θ y
  have hL := mfderiv_comp (I' := 𝓘(ℝ, ℝ)) x
    (((contMDiff_circleInterp_slice hG hG1 θ).mdifferentiable (by simp)) _)
    ((AddCircle.contMDiff_coe.mdifferentiable (by simp)) x)
  have hlin := hasDerivAt_lineInterp hG θ x
  have hR := mfderiv_comp (I' := 𝓘(ℝ, ℝ)) x
    ((AddCircle.contMDiff_coe.mdifferentiable (by simp)) (lineInterp G (θ, x)))
    hlin.differentiableAt.mdifferentiableAt
  rw [hcomp, hR, hlin.hasFDerivAt.hasMFDerivAt.mfderiv] at hL
  let g := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (circleInterp hG1 θ) (x : AddCircle (1 : ℝ))
  let D := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) x
  let D' := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) (lineInterp G (θ, x))
  have hgD : ∀ u : ℝ, g (D u) = D' (u * d) := by
    intro u
    have hu := congrArg (fun L => L u) hL
    change D' (u * d) = g (D u) at hu
    exact hu.symm
  have hDb := AddCircle.bijective_mfderiv_coe x
  have hD'b := AddCircle.bijective_mfderiv_coe (lineInterp G (θ, x))
  constructor
  · intro a b hab
    obtain ⟨a', rfl⟩ := hDb.2 a
    obtain ⟨b', rfl⟩ := hDb.2 b
    have h1 : D' ((show ℝ from a') * d) = D' ((show ℝ from b') * d) := by
      rw [← hgD, ← hgD]
      exact hab
    have h2 := hD'b.1 h1
    have h3 : (show ℝ from a') = (show ℝ from b') := mul_right_cancel₀ hd0 h2
    exact congrArg D h3
  · intro w
    obtain ⟨c, hc⟩ := hD'b.2 w
    refine ⟨D ((show ℝ from c) / d), ?_⟩
    rw [hgD, div_mul_cancel₀ _ hd0]
    exact hc

end Interpolation

section TorusParam

open DifferentialGeometry.Topology.Ehresmann.CircleFibre

/-- **Torus parametrization from a cut with orientation-preserving monodromy.** -/
theorem exists_torus_param_of_positive_cut {S : Type u} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    (p : S → Circle) (hp : ContMDiff (𝓡 2) (𝓡 1) ∞ p) (Ψ : AddCircle (1 : ℝ) × ℝ → S)
    (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ Ψ)
    (hΨbij : ∀ q, Bijective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) Ψ q))
    (hpΨ : ∀ q, p (Ψ q) = Circle.exp (2 * Real.pi * q.2))
    (φ : AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ AddCircle (1 : ℝ))
    (hper : ∀ z s, Ψ (z, s + 1) = Ψ (φ z, s))
    (hinj : InjOn Ψ (univ ×ˢ Ico (0 : ℝ) (0 + 1)))
    (hsurj : ∀ x, ∃ z, ∃ t ∈ Ico (0 : ℝ) (0 + 1), Ψ (z, t) = x)
    (F : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ) (hF1 : ∀ t, F (t + 1) = F t + 1) (hF' : ∀ t, 0 < deriv F t)
    (hpos : ∀ t : ℝ, φ (t : AddCircle (1 : ℝ)) = (F t : AddCircle (1 : ℝ))) :
    ∃ e : Torus ≃ₘ⟮torusModel, 𝓡 2⟯ S, ∀ t, p (e t) = t.1 := by
  classical
  let G : ℝ → ℝ := F.symm
  have hG : ContDiff ℝ ∞ G := F.symm.contMDiff.contDiff
  have hFG : ∀ t, F (G t) = t := fun t => F.apply_symm_apply t
  have hG1 : ∀ t, G (t + 1) = G t + 1 := by
    intro t
    have h := hF1 (G t)
    rw [hFG] at h
    rw [← h]
    exact F.symm_apply_apply (G t + 1)
  have hG' : ∀ t, 0 < deriv G t := by
    intro t
    have hFd := (F.contMDiff.contDiff.differentiable (by simp) (G t)).hasDerivAt
    have hGd := (hG.differentiable (by simp) t).hasDerivAt
    have hcomp := hFd.comp t hGd
    have hid : (F ∘ G) = id := funext hFG
    rw [hid] at hcomp
    have h1 := hcomp.unique (hasDerivAt_id t)
    have h2 := hF' (G t)
    by_contra hle
    push Not at hle
    nlinarith
  let CI := circleInterp hG1
  let E : ℝ × AddCircle (1 : ℝ) → S := fun q => Ψ (CI q.1 q.2, q.1)
  have hE : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ E :=
    hΨ.comp ((contMDiff_circleInterp hG hG1).prodMk contMDiff_fst)
  have hEper : ∀ θ ∈ Icc (-1 / 3 : ℝ) (1 / 3), ∀ z, E (θ + 1, z) = E (θ, z) := by
    intro θ hθ z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    have h1 : CI (θ + 1) (x : AddCircle (1 : ℝ)) = (G x : AddCircle (1 : ℝ)) := by
      change circleInterp hG1 (θ + 1) (x : AddCircle (1 : ℝ)) = _
      rw [circleInterp_coe]
      simp only [lineInterp, stepThirds_of_ge (show 2 / 3 ≤ θ + 1 by linarith [hθ.1]), sub_self,
        zero_mul, one_mul, zero_add]
    have h0 : CI θ (x : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ)) := by
      change circleInterp hG1 θ (x : AddCircle (1 : ℝ)) = _
      rw [circleInterp_coe]
      simp only [lineInterp, stepThirds_of_le hθ.2, sub_zero, one_mul, zero_mul, add_zero]
    change Ψ (CI (θ + 1) (x : AddCircle (1 : ℝ)), θ + 1) = Ψ (CI θ (x : AddCircle (1 : ℝ)), θ)
    rw [h1, h0, hper, hpos, hFG]
  let e₀ : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) → S := fun q => E (angleLift 0 q.1, q.2)
  have hE₀ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ e₀ := by
    rintro ⟨y, z⟩
    by_cases hy : y = ((0 : ℝ) : AddCircle (1 : ℝ))
    · have hy' : y ≠ ((-1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
        rw [hy]
        intro h
        have h2 := congrArg (angleLift (-1 / 2)) h
        rw [angleLift_coe (show (0 : ℝ) ∈ Ico (-1 / 2) (-1 / 2 + 1) by norm_num),
          angleLift_coe (show (-1 / 2 : ℝ) ∈ Ico (-1 / 2) (-1 / 2 + 1) by norm_num)] at h2
        norm_num at h2
      let e₁ : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) → S :=
        fun q => E (angleLift (-1 / 2) q.1, q.2)
      have he₁ : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ e₁ (y, z) :=
        hE.contMDiffAt.comp (y, z)
          (((contMDiffAt_angleLift hy').comp (y, z) contMDiffAt_fst).prodMk contMDiffAt_snd)
      apply he₁.congr_of_eventuallyEq
      have hval : angleLift (-1 / 2) y = 0 := by
        rw [hy]
        exact angleLift_coe (show (0 : ℝ) ∈ Ico (-1 / 2) (-1 / 2 + 1) by norm_num)
      have hnhd : ∀ᶠ q in 𝓝 ((y, z) : AddCircle (1 : ℝ) × AddCircle (1 : ℝ)),
          angleLift (-1 / 2) q.1 ∈ Ioo (-1 / 3 : ℝ) (1 / 3) := by
        have hc : ContinuousAt (fun q : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
            angleLift (-1 / 2) q.1) (y, z) :=
          ContinuousAt.comp (g := angleLift (-1 / 2))
            (f := fun q : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => q.1)
            (contMDiffAt_angleLift hy').continuousAt continuousAt_fst
        exact hc.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by rw [hval]; norm_num))
      filter_upwards [hnhd] with q hq
      have hcoe : ((angleLift (-1 / 2) q.1 : ℝ) : AddCircle (1 : ℝ)) = q.1 :=
        coe_angleLift _ _
      change E (angleLift 0 q.1, q.2) = E (angleLift (-1 / 2) q.1, q.2)
      by_cases h0 : 0 ≤ angleLift (-1 / 2) q.1
      · have h' : angleLift 0 q.1 = angleLift (-1 / 2) q.1 := by
          conv_lhs => rw [← hcoe]
          exact angleLift_coe ⟨h0, by linarith [hq.2]⟩
        rw [h']
      · push Not at h0
        have h' : angleLift 0 q.1 = angleLift (-1 / 2) q.1 + 1 := by
          have hc1 : (((angleLift (-1 / 2) q.1 + 1 : ℝ)) : AddCircle (1 : ℝ)) = q.1 := by
            rw [AddCircle.coe_add, AddCircle.coe_period, add_zero, hcoe]
          conv_lhs => rw [← hc1]
          exact angleLift_coe ⟨by linarith [hq.1], by linarith⟩
        rw [h']
        exact hEper _ ⟨hq.1.le, hq.2.le⟩ q.2
    · exact hE.contMDiffAt.comp (y, z)
        (((contMDiffAt_angleLift hy).comp (y, z) contMDiffAt_fst).prodMk contMDiffAt_snd)
  let dC := AddCircle.diffeomorphCircle
  have hpe : ∀ q, p (e₀ q) = dC q.1 := by
    intro q
    change p (Ψ (CI (angleLift 0 q.1) q.2, angleLift 0 q.1)) = dC q.1
    rw [hpΨ]
    conv_rhs => rw [← coe_angleLift 0 q.1]
    exact (diffeomorphCircle_coe _).symm
  have he₀inj : Injective e₀ := by
    rintro ⟨y, z⟩ ⟨y', z'⟩ h
    have hy : y = y' := dC.injective ((hpe (y, z)).symm.trans ((congrArg p h).trans
      (hpe (y', z'))))
    subst hy
    have hθ : angleLift 0 y ∈ Ico (0 : ℝ) (0 + 1) := angleLift_mem_Ico 0 y
    have h2 : Ψ (CI (angleLift 0 y) z, angleLift 0 y) = Ψ (CI (angleLift 0 y) z', angleLift 0 y) :=
      h
    have h3 := hinj ⟨mem_univ _, hθ⟩ ⟨mem_univ _, hθ⟩ h2
    have h4 : CI (angleLift 0 y) z = CI (angleLift 0 y) z' := (Prod.ext_iff.mp h3).1
    rw [injective_circleInterp hG hG' hG1 _ h4]
  have he₀surj : Surjective e₀ := by
    intro x
    obtain ⟨w, t, ht, hwt⟩ := hsurj x
    obtain ⟨z, hz⟩ := surjective_circleInterp hG hG1 t w
    refine ⟨((t : AddCircle (1 : ℝ)), z), ?_⟩
    change Ψ (CI (angleLift 0 (t : AddCircle (1 : ℝ))) z, angleLift 0 (t : AddCircle (1 : ℝ))) = x
    rw [angleLift_coe ht]
    change Ψ (circleInterp hG1 t z, t) = x
    rw [hz, hwt]
  have hCI : ∀ θ, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (CI θ) :=
    fun θ => contMDiff_circleInterp_slice hG hG1 θ
  have he₀imm : ∀ q, Injective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) e₀ q) := by
    rintro ⟨y, z⟩
    rw [injective_iff_map_eq_zero]
    intro v hv
    set θ := angleLift 0 y with hθ
    have hd₀ : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) e₀ (y, z) :=
      (hE₀ (y, z)).mdifferentiableAt (by simp)
    -- the first component vanishes
    have hv1 : (show ℝ × ℝ from v).1 = 0 := by
      have hpe' : (p ∘ e₀) = (dC ∘ Prod.fst) := funext hpe
      have hc1 := mfderiv_comp (y, z) ((hp (e₀ (y, z))).mdifferentiableAt (by simp)) hd₀
      have hc2 := mfderiv_comp (f := Prod.fst) (g := (dC : AddCircle (1 : ℝ) → Circle)) (y, z)
        ((dC.contMDiff.mdifferentiable (by simp)) y)
        (mdifferentiableAt_fst (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (x := (y, z)))
      rw [hpe', hc2, mfderiv_fst] at hc1
      have h := congrArg (fun L => L v) hc1
      change mfderiv 𝓘(ℝ, ℝ) (𝓡 1) dC y (show ℝ × ℝ from v).1 =
        mfderiv (𝓡 2) (𝓡 1) p (e₀ (y, z)) (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) e₀ (y, z) v)
        at h
      rw [hv, map_zero] at h
      exact (dC.mfderivToContinuousLinearEquiv (by simp) y).injective (h.trans (map_zero _).symm)
    -- the second component vanishes
    have hslice : (e₀ ∘ fun z' : AddCircle (1 : ℝ) => (y, z')) =
        (fun w : AddCircle (1 : ℝ) => Ψ (w, θ)) ∘ CI θ := rfl
    have hpair : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
        (fun z' : AddCircle (1 : ℝ) => (y, z')) z :=
      mdifferentiableAt_const.prodMk mdifferentiableAt_id
    have hc3 := mfderiv_comp z hd₀ hpair
    rw [mfderiv_prod_right] at hc3
    have hΨd : ∀ w : AddCircle (1 : ℝ), MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2)
        (fun w : AddCircle (1 : ℝ) => Ψ (w, θ)) w := fun w =>
      ((hΨ (w, θ)).mdifferentiableAt (by simp)).comp w
        (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    have hc4 := mfderiv_comp z (hΨd (CI θ z)) (((hCI θ) z).mdifferentiableAt (by simp))
    have hpair' : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
        (fun w : AddCircle (1 : ℝ) => (w, θ)) (CI θ z) :=
      mdifferentiableAt_id.prodMk mdifferentiableAt_const
    have hc5 := mfderiv_comp (CI θ z) ((hΨ (CI θ z, θ)).mdifferentiableAt (by simp)) hpair'
    rw [mfderiv_prod_left] at hc5
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun w : AddCircle (1 : ℝ) => Ψ (w, θ)) (CI θ z) = _ at hc5
    rw [hslice, hc4, hc5] at hc3
    have h := congrArg (fun L => L (show ℝ × ℝ from v).2) hc3
    have hv' : (show ℝ × ℝ from v) = (0, (show ℝ × ℝ from v).2) := Prod.ext hv1 rfl
    change mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) Ψ (CI θ z, θ)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (CI θ) z (show ℝ × ℝ from v).2, 0) =
      mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) e₀ (y, z) (0, (show ℝ × ℝ from v).2) at h
    rw [← hv', hv] at h
    have h2 := (hΨbij (CI θ z, θ)).1 (h.trans (map_zero _).symm)
    have h3 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (CI θ) z (show ℝ × ℝ from v).2 = 0 :=
      (Prod.ext_iff.mp h2).1
    have h4 := (bijective_mfderiv_circleInterp hG hG' hG1 θ z).1 (h3.trans (map_zero _).symm)
    exact hv'.trans (Prod.ext rfl h4)
  have hloc : IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ e₀ :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv e₀ hE₀
      he₀imm (by simp)
  let e₀d := hloc.diffeomorphOfBijective ⟨he₀inj, he₀surj⟩
  let P : Torus ≃ₘ⟮torusModel, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :=
    { toEquiv := dC.symm.toEquiv.prodCongr dC.symm.toEquiv
      contMDiff_toFun := (dC.symm.contMDiff.comp contMDiff_fst).prodMk
        (dC.symm.contMDiff.comp contMDiff_snd)
      contMDiff_invFun := (dC.contMDiff.comp contMDiff_fst).prodMk
        (dC.contMDiff.comp contMDiff_snd) }
  refine ⟨P.trans e₀d, fun t => ?_⟩
  change p (e₀ (dC.symm t.1, dC.symm t.2)) = t.1
  rw [hpe]
  exact dC.apply_symm_apply t.1

end TorusParam

section Param

/-- **B2-param (V3).** An oriented closed surface fibred over the circle with connected fibres is
an actual torus, with the projection read as the first factor. Route: the fibre over `1` is an
actual circle (regular fibre); ASM-L3's cut along it (`CircleFibre.exists_circleCut`) gives the
local diffeomorphism `Ψ : S¹ × ℝ → S` with monodromy `φ`; the monodromy lift is increasing or
decreasing (`AddCircle.exists_increasing_diffeomorphism_lift_or_neg`); the decreasing case is
excluded by the orientation (`false_of_neg_monodromy_lift`); in the increasing case the convex
interpolation of the lift of `φ⁻¹` with the identity (positive derivative, flattened at the time
ends by `stepThirds`) gives the torus map, glued at the cut (`exists_torus_param_of_positive_cut`).

V2 → V3 (main's decision): the frozen V1/V2 statement carried `[ConnectedSpace S]`, which is
redundant. Every fibre is connected and nonempty (`hfib`); if `S = S₁ ⊔ S₂` with both parts
nonempty, open and closed, then each `p (Sᵢ)` is open (submersion) and closed (compact) in the
connected circle, hence all of it, so every fibre meets both parts and is disconnected. The
instance is therefore dropped. -/
theorem exists_torus_param_of_circle_fibred_surface {S : Type u} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S] [CompactSpace S]
    [T2Space S] (o : ManifoldOrientation (𝓡 2) S 2)
    (p : S → Circle) (hp : ContMDiff (𝓡 2) (𝓡 1) ∞ p)
    (hsub : ∀ x, Surjective (mfderiv (𝓡 2) (𝓡 1) p x))
    (hfib : ∀ z, IsConnected (p ⁻¹' {z})) :
    ∃ e : Torus ≃ₘ⟮torusModel, 𝓡 2⟯ S, ∀ t, p (e t) = t.1 := by
  obtain ⟨f, hf, hr⟩ := exists_addCircle_fibre_embedding p hp hsub (hfib 1)
  obtain ⟨Ψ, φ, hΨ, -, hpΨ, hper, hinj, hsurj, hstrip⟩ :=
    DifferentialGeometry.Topology.Ehresmann.CircleFibre.exists_circleCut p hp hsub f hf hr
  have hΨbij : ∀ q, Bijective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) Ψ q) := by
    intro q
    obtain ⟨d, hds, hdf⟩ := hstrip 0 1 (q.2 - 1 / 2) (q.2 + 1 / 2) one_pos (by linarith)
    have hq : q ∈ d.source := by
      rw [hds]
      exact ⟨mem_univ _, by constructor <;> linarith⟩
    have hdΨ : (d : AddCircle (1 : ℝ) × ℝ → S) = Ψ := by
      rw [hdf]
      funext q'
      simp
    have hloc : IsLocalDiffeomorphAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ Ψ q :=
      hdΨ ▸ d.isLocalDiffeomorphAt _ _ _ hq
    obtain ⟨e, he⟩ := hloc.isInvertible_mfderiv (by simp)
    rw [← he]
    exact e.bijective
  obtain ⟨F, hF1, hF', hcase⟩ := AddCircle.exists_increasing_diffeomorphism_lift_or_neg φ
  rcases hcase with hpos | hneg
  · exact exists_torus_param_of_positive_cut p hp Ψ hΨ hΨbij hpΨ φ hper (hinj 0) (hsurj 0) F hF1
      hF' hpos
  · exact (false_of_neg_monodromy_lift o Ψ hΨ hΨbij φ hper F hF1 hF' hneg).elim

end Param

end GC.GraphManifold.Assembly
