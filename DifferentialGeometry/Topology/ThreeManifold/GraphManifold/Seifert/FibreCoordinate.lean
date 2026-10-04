import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BundleOverAnnulus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BundleOverDiscGlobal
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Decomposition
import DifferentialGeometry.Topology.Manifold.ProductOrientationCongruence
import DifferentialGeometry.Topology.Manifold.DiffeomorphOrientationDichotomy
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.HalfSpaceExtension

/-!
# Fibre coordinates of a circle fibration

Chapter 6, lane MD4 of the P1 Morse-decomposition plan
(`docs/geometrization/handoffs/20261003-survey-p1-morse-decomposition.md`, §3).

A `FibreCoordinate F V` over an open set `V` of the base of a circle fibration `F` is a
diffeomorphism `π⁻¹ V ≃ V × S¹` over the projection (`fst_eq`), the shape of the charts of
`GM/Presentation.lean`. It is `IsPositive` for an orientation `o` of `V` when it carries the
orientation of the total space to `o × circleOrientation`. A `LiftedBicollar F c` is a smooth
flow of the total space (zero time, composition, inverse by `Diffeomorph`) covering a flow of
the base that moves points of a bicollar `c : S¹ × ℝ → base` along the `ℝ`-lines of `c` for
`|s| < width` (`baseFlow_apply`) and fixes everything off `c (S¹ × [-reach, reach])`
(`baseFlow_eq_self`, `flow_eq_self`), the transverse data the sweep and the seams use.

Positivity (review 8, item 5): `preservesOrientation_or_opposite` holds for diffeomorphisms
between connected manifolds over arbitrary models, boundary included, so `exists_isPositive`
replaces `τ` by `τ` or `τ.conj`; positivity is local (`isPositive_of_local`).

Flow normalisation (review 8, item 1): `flowNormalize` changes `τ` only over
`c (S¹ × (-ε, ε))` (`0 < ε ≤ width`, that collar inside `V`) by the explicit formula
`τ'⁻¹ (b, v) = flow (m b) (τ⁻¹ (pull b, v))`, `m = s · bump(s)`, and gives
`τ'⁻¹ (c (θ, s), v) = flow s (τ'⁻¹ (c (θ, 0), v))` for `|s| < ε / 4` on both sides of the seam.
A one-sided version that leaves the other side unchanged is false (smoothness at `s = 0`).

Gluing (review 8, items 2 and 3): on each simply connected component `O'` of `V₁ ∩ V₂` the
transition `τ₂ ∘ τ₁⁻¹` is lifted on `O' × ℝ` (`transitionLift`), is periodic
(`transitionLift_add_one`) and has positive fibre derivative (`deriv_transitionLift_pos`, from
the positivity of both coordinates via `orientation_map_fibrewise_lift`). The interpolation
`(1 - ℓ) t + ℓ K` with `0 ≤ ℓ ≤ 1` has positive derivative, its inverse is jointly smooth over a
base with boundary (`contMDiffOn_inverse_param`: half-plane extension and the parameterised
inverse function theorem), and `glue` assembles a positive coordinate over `V₁ ∪ V₂` equal to
`τ₁` where `ℓ (π x) = 0` and to `τ₂` where `ℓ (π x) = 1`.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

structure FibreCoordinate (F : CircleFibration C U)
    (V : TopologicalSpace.Opens F.base.Carrier) where
  toDiffeo : TopologicalSpace.Opens.comap F.projection V
    ≃ₘ⟮C.model, (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ (V × Circle)
  fst_eq : ∀ x, ((toDiffeo x).1).val = F.projection x.val

def CircleFibration.totalOrientation (F : CircleFibration C U)
    (V : TopologicalSpace.Opens F.base.Carrier) :
    ManifoldOrientation C.model (TopologicalSpace.Opens.comap F.projection V) 3 :=
  (C.orientation.restrictOpen U).restrictOpen (TopologicalSpace.Opens.comap F.projection V)

def CircleFibration.productOrientation (F : CircleFibration C U)
    (V : TopologicalSpace.Opens F.base.Carrier)
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) V 2) :
    ManifoldOrientation ((SurfaceModel.model F.base.kind).prod (𝓡 1)) (V × Circle) 3 :=
  DifferentialGeometry.productOrientation (SurfaceModel.model F.base.kind) (𝓡 1) (by norm_num)
    le_rfl o circleOrientation

def FibreCoordinate.IsPositive {F : CircleFibration C U} {V : TopologicalSpace.Opens F.base.Carrier}
    (τ : FibreCoordinate F V) (o : ManifoldOrientation (SurfaceModel.model F.base.kind) V 2) :
    Prop :=
  τ.toDiffeo.preservesOrientation (CircleFibration.totalOrientation F V)
    (CircleFibration.productOrientation F V o)

def circleInvDiffeo : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle where
  toEquiv := Equiv.inv Circle
  contMDiff_toFun := contMDiff_inv (𝓡 1) ∞
  contMDiff_invFun := contMDiff_inv (𝓡 1) ∞

def FibreCoordinate.conj {F : CircleFibration C U} {V : TopologicalSpace.Opens F.base.Carrier}
    (τ : FibreCoordinate F V) : FibreCoordinate F V where
  toDiffeo := τ.toDiffeo.trans
    ((Diffeomorph.refl (SurfaceModel.model F.base.kind) V ∞).prodCongr circleInvDiffeo)
  fst_eq x := τ.fst_eq x

structure LiftedBicollar (F : CircleFibration C U)
    (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
      (Circle × ℝ) F.base.Carrier ∞) where
  flow : ℝ → (U ≃ₘ⟮C.model, C.model⟯ U)
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod C.model) C.model ∞ (fun p : ℝ × U => flow p.1 p.2)
  flow_zero : ∀ x, flow 0 x = x
  flow_add : ∀ s t x, flow (s + t) x = flow s (flow t x)
  baseFlow : ℝ → F.base.Carrier → F.base.Carrier
  projection_flow : ∀ r x, F.projection (flow r x) = baseFlow r (F.projection x)
  width : ℝ
  width_pos : 0 < width
  reach : ℝ
  width_lt_reach : width < reach
  mem_source : ∀ θ s, |s| ≤ reach → (θ, s) ∈ c.source
  baseFlow_apply : ∀ θ s r, |s| < width → |s + r| < width → baseFlow r (c (θ, s)) = c (θ, s + r)
  baseFlow_eq_self : ∀ r b, (∀ θ s, |s| ≤ reach → b ≠ c (θ, s)) → baseFlow r b = b
  flow_eq_self : ∀ r x, (∀ θ s, |s| ≤ reach → F.projection x ≠ c (θ, s)) → flow r x = x

namespace FibreCoordinate

variable {F : CircleFibration C U} {V W : TopologicalSpace.Opens F.base.Carrier}

theorem projection_symm (τ : FibreCoordinate F V) (q : V × Circle) :
    F.projection (τ.toDiffeo.symm q).val = q.1.val := by
  rw [← τ.fst_eq, Diffeomorph.apply_symm_apply]

open scoped Classical in
def angle (τ : FibreCoordinate F V) (x : U) : Circle :=
  if hx : F.projection x ∈ V then (τ.toDiffeo ⟨x, hx⟩).2 else 1

theorem angle_of_mem (τ : FibreCoordinate F V) (x : U) (hx : F.projection x ∈ V) :
    τ.angle x = (τ.toDiffeo ⟨x, hx⟩).2 :=
  dite_eq_left hx

theorem toDiffeo_apply (τ : FibreCoordinate F V) (x : TopologicalSpace.Opens.comap F.projection V) :
    τ.toDiffeo x = (⟨F.projection x.val, x.2⟩, τ.angle x.val) :=
  Prod.ext (Subtype.ext (τ.fst_eq x)) (τ.angle_of_mem x.val x.2).symm

theorem angle_symm (τ : FibreCoordinate F V) (q : V × Circle) :
    τ.angle (τ.toDiffeo.symm q).val = q.2 := by
  rw [τ.angle_of_mem _ (τ.toDiffeo.symm q).2]
  exact congrArg Prod.snd (τ.toDiffeo.apply_symm_apply q)

theorem symm_angle (τ : FibreCoordinate F V) (x : U) (hx : F.projection x ∈ V) :
    (τ.toDiffeo.symm (⟨F.projection x, hx⟩, τ.angle x)).val = x := by
  have h := τ.toDiffeo_apply ⟨x, hx⟩
  rw [← h, Diffeomorph.symm_apply_apply]

theorem isOpen_preimage (V : TopologicalSpace.Opens F.base.Carrier) :
    IsOpen (F.projection ⁻¹' (V : Set F.base.Carrier)) :=
  V.isOpen.preimage F.projection.continuous

theorem contMDiffOn_angle (τ : FibreCoordinate F V) :
    ContMDiffOn C.model (𝓡 1) ∞ τ.angle (F.projection ⁻¹' (V : Set F.base.Carrier)) := by
  intro x hx
  have h : ContMDiffAt C.model (𝓡 1) ∞
      (fun y : TopologicalSpace.Opens.comap F.projection V => τ.angle y.val) ⟨x, hx⟩ := by
    have he : (fun y : TopologicalSpace.Opens.comap F.projection V => τ.angle y.val) =
        fun y => (τ.toDiffeo y).2 := funext fun y => τ.angle_of_mem y.val y.2
    rw [he]
    exact (contMDiff_snd.comp τ.toDiffeo.contMDiff).contMDiffAt
  exact (contMDiffAt_subtype_iff.mp h).contMDiffWithinAt

theorem contMDiff_symm_val (τ : FibreCoordinate F V) :
    ContMDiff ((SurfaceModel.model F.base.kind).prod (𝓡 1)) C.model ∞
      (fun q : V × Circle => (τ.toDiffeo.symm q).val) :=
  contMDiff_subtype_val.comp τ.toDiffeo.symm.contMDiff

def ofAngle (V : TopologicalSpace.Opens F.base.Carrier) (θ : U → Circle) (σ : V × Circle → U)
    (hθ : ContMDiffOn C.model (𝓡 1) ∞ θ (F.projection ⁻¹' (V : Set F.base.Carrier)))
    (hσ : ContMDiff ((SurfaceModel.model F.base.kind).prod (𝓡 1)) C.model ∞ σ)
    (hπσ : ∀ q, F.projection (σ q) = q.1.val) (hθσ : ∀ q, θ (σ q) = q.2)
    (hσθ : ∀ (x : U) (hx : F.projection x ∈ V), σ (⟨F.projection x, hx⟩, θ x) = x) :
    FibreCoordinate F V where
  toDiffeo :=
    { toFun := fun x => (⟨F.projection x.val, x.2⟩, θ x.val)
      invFun := fun q => ⟨σ q, by
        change F.projection (σ q) ∈ V
        rw [hπσ]
        exact q.1.2⟩
      left_inv := fun x => Subtype.ext (hσθ x.val x.2)
      right_inv := fun q => Prod.ext (Subtype.ext (hπσ q)) (hθσ q)
      contMDiff_toFun := by
        refine ContMDiff.prodMk ?_ ?_
        · apply (ContMDiff.subtypeVal_comp_iff V _).mp
          exact F.smooth.comp contMDiff_subtype_val
        · intro x
          exact (hθ x.val x.2).contMDiffAt ((isOpen_preimage V).mem_nhds x.2) |>.comp x
            contMDiff_subtype_val.contMDiffAt
      contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp hσ }
  fst_eq x := rfl

theorem angle_ofAngle (V : TopologicalSpace.Opens F.base.Carrier) (θ : U → Circle)
    (σ : V × Circle → U)
    (hθ : ContMDiffOn C.model (𝓡 1) ∞ θ (F.projection ⁻¹' (V : Set F.base.Carrier)))
    (hσ : ContMDiff ((SurfaceModel.model F.base.kind).prod (𝓡 1)) C.model ∞ σ)
    (hπσ : ∀ q, F.projection (σ q) = q.1.val) (hθσ : ∀ q, θ (σ q) = q.2)
    (hσθ : ∀ (x : U) (hx : F.projection x ∈ V), σ (⟨F.projection x, hx⟩, θ x) = x)
    (x : U) (hx : F.projection x ∈ V) :
    (ofAngle V θ σ hθ hσ hπσ hθσ hσθ).angle x = θ x := by
  rw [angle_of_mem _ x hx]
  rfl

theorem symm_ofAngle (V : TopologicalSpace.Opens F.base.Carrier) (θ : U → Circle)
    (σ : V × Circle → U)
    (hθ : ContMDiffOn C.model (𝓡 1) ∞ θ (F.projection ⁻¹' (V : Set F.base.Carrier)))
    (hσ : ContMDiff ((SurfaceModel.model F.base.kind).prod (𝓡 1)) C.model ∞ σ)
    (hπσ : ∀ q, F.projection (σ q) = q.1.val) (hθσ : ∀ q, θ (σ q) = q.2)
    (hσθ : ∀ (x : U) (hx : F.projection x ∈ V), σ (⟨F.projection x, hx⟩, θ x) = x)
    (q : V × Circle) :
    ((ofAngle V θ σ hθ hσ hπσ hθσ hσθ).toDiffeo.symm q).val = σ q :=
  rfl

def ofTrivialization (F : CircleFibration C U) (b : F.base.Carrier) :
    FibreCoordinate F (F.neighborhood b) :=
  ⟨F.trivialization b, F.projection_trivialization b⟩

theorem mem_neighborhood (F : CircleFibration C U) (b : F.base.Carrier) :
    b ∈ F.neighborhood b :=
  F.mem_neighborhood b

def restrict (τ : FibreCoordinate F V) (hWV : W ≤ V) : FibreCoordinate F W :=
  ⟨CircleFibration.restrictChart F hWV τ.toDiffeo τ.fst_eq,
    CircleFibration.restrictChart_fst F hWV τ.toDiffeo τ.fst_eq⟩

theorem angle_restrict (τ : FibreCoordinate F V) (hWV : W ≤ V) (x : U)
    (hx : F.projection x ∈ W) : (τ.restrict hWV).angle x = τ.angle x := by
  rw [angle_of_mem _ x hx, τ.angle_of_mem x (hWV hx)]
  exact CircleFibration.restrictChart_snd F hWV τ.toDiffeo τ.fst_eq x hx

theorem symm_restrict (τ : FibreCoordinate F V) (hWV : W ≤ V) (q : W × Circle) :
    ((τ.restrict hWV).toDiffeo.symm q).val =
      (τ.toDiffeo.symm (TopologicalSpace.Opens.inclusion hWV q.1, q.2)).val :=
  rfl

theorem angle_conj (τ : FibreCoordinate F V) (x : U) (hx : F.projection x ∈ V) :
    τ.conj.angle x = (τ.angle x)⁻¹ := by
  rw [angle_of_mem _ x hx, τ.angle_of_mem x hx]
  rfl

theorem exists_mem_nhds (F : CircleFibration C U) (b : F.base.Carrier)
    {N : Set F.base.Carrier} (hN : N ∈ 𝓝 b) :
    ∃ V : TopologicalSpace.Opens F.base.Carrier, b ∈ V ∧ (V : Set F.base.Carrier) ⊆ N ∧
      Nonempty (FibreCoordinate F V) := by
  obtain ⟨O, hON, hO, hbO⟩ := mem_nhds_iff.mp hN
  let V : TopologicalSpace.Opens F.base.Carrier := ⟨O, hO⟩ ⊓ F.neighborhood b
  exact ⟨V, ⟨hbO, F.mem_neighborhood b⟩, fun y hy => hON hy.1,
    ⟨(ofTrivialization F b).restrict inf_le_right⟩⟩

end FibreCoordinate

section Orientation

theorem productTangentBasis_orientation_neg_right {E E' H H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace H' N] {m n : ℕ} {x : M} {y : N}
    (b : Module.Basis (Fin m) ℝ (TangentSpace I x)) (c : Module.Basis (Fin n) ℝ (TangentSpace J y))
    (i : Fin n) :
    (productTangentBasis I J b (c.unitsSMul (Function.update 1 i (-1)))).orientation
      = -(productTangentBasis I J b c).orientation := by
  have hbp : b.prod (c.unitsSMul (Function.update 1 i (-1)))
      = (b.prod c).unitsSMul (Function.update 1 (Sum.inr i) (-1)) := by
    ext j <;> cases j <;>
      simp only [Module.Basis.unitsSMul_apply, Module.Basis.prod_apply, Function.update_apply,
        Sum.elim_inl, Sum.elim_inr] <;>
      (split_ifs <;> simp_all [Module.Basis.unitsSMul_apply, Units.smul_def])
  rw [productTangentBasis_orientation_eq, productTangentBasis_orientation_eq, hbp,
    Module.Basis.orientation_reindex, Module.Basis.orientation_reindex,
    Module.Basis.orientation_neg_single, Orientation.reindex_neg]
  rfl

theorem productOrientation_opposite_right {E E' H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [IsManifold I ∞ M] [IsManifold J ∞ N] {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (oM : ManifoldOrientation I M m) (oN : ManifoldOrientation J N n) :
    (DifferentialGeometry.productOrientation I J hm hn oM oN).opposite
      = DifferentialGeometry.productOrientation I J hm hn oM oN.opposite := by
  refine productOrientation_unique I J hm hn oM oN.opposite
    (DifferentialGeometry.productOrientation I J hm hn oM oN).opposite ?_
  intro x y b c hb hc
  have hc1 : (c.unitsSMul (Function.update 1 (⟨0, hn⟩ : Fin n) (-1))).orientation
      = oN.orientation y := by
    rw [Module.Basis.orientation_neg_single, hc, ManifoldOrientation.opposite_orientation]
    exact neg_neg (oN.orientation y)
  have hchar := productOrientation_characterization I J hm hn oM oN x y b
    (c.unitsSMul (Function.update 1 (⟨0, hn⟩ : Fin n) (-1))) hb hc1
  rw [ManifoldOrientation.opposite_orientation, ← hchar,
    productTangentBasis_orientation_neg_right b c ⟨0, hn⟩]
  exact (neg_neg ((productTangentBasis I J b c).orientation)).symm

theorem mfderiv_circleInv_apply (v : EuclideanSpace ℝ (Fin 1)) :
    mfderiv (𝓡 1) (𝓡 1) (fun z : Circle => z⁻¹) 1 v = -v := by
  have hloc := AnnulusStraightening.isLocalDiffeomorph_cexp 0
  have hAinv : (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) AnnulusStraightening.cexp 0).IsInvertible :=
    hloc.isInvertible_mfderiv (by simp)
  obtain ⟨e, he⟩ := hAinv
  have hinv : ∀ z : Circle, MDifferentiableAt (𝓡 1) (𝓡 1) (fun z : Circle => z⁻¹) z :=
    fun z => ((contMDiff_inv (𝓡 1) ∞).mdifferentiable (by simp)) z
  have hcexp : ∀ t : ℝ, MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) AnnulusStraightening.cexp t :=
    fun t => (AnnulusStraightening.contMDiff_cexp.mdifferentiable (by simp)) t
  have hneg : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => -t) 0 :=
    ((contDiff_neg (n := ∞)).contMDiff.mdifferentiable (by simp)) 0
  have hcomp : (fun z : Circle => z⁻¹) ∘ AnnulusStraightening.cexp =
      AnnulusStraightening.cexp ∘ fun t => -t :=
    funext fun t => (AnnulusStraightening.cexp_neg t).symm
  have hnegd : ∀ s : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ),
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => -t) 0 s = -s := by
    intro s
    have h : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => -t) 0 (-ContinuousLinearMap.id ℝ ℝ) :=
      ((hasFDerivAt_id (0 : ℝ)).neg).hasMFDerivAt
    rw [h.mfderiv]
    rfl
  obtain ⟨t, rfl⟩ : ∃ t : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ),
      mfderiv 𝓘(ℝ, ℝ) (𝓡 1) AnnulusStraightening.cexp 0 t = v :=
    ⟨e.symm v, by rw [← he]; exact e.apply_symm_apply v⟩
  have key : mfderiv (𝓡 1) (𝓡 1) (fun z : Circle => z⁻¹) (AnnulusStraightening.cexp 0)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) AnnulusStraightening.cexp 0 t) =
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) AnnulusStraightening.cexp 0 (-t) := by
    rw [← mfderiv_comp_apply (0 : ℝ) (hinv _) (hcexp 0), hcomp,
      mfderiv_comp_apply_of_eq (0 : ℝ) (hcexp 0) hneg neg_zero, hnegd]
  have h1 : (1 : Circle) = AnnulusStraightening.cexp 0 := AnnulusStraightening.cexp_zero.symm
  rw [h1, key, map_neg]
  rfl

theorem circleInvDiffeo_preservesOrientation :
    circleInvDiffeo.preservesOrientation circleOrientation circleOrientation.opposite := by
  rcases circleInvDiffeo.preservesOrientation_or_preservesOrientation_opposite circleOrientation
    circleOrientation with h | h
  · exfalso
    let E1 := EuclideanSpace ℝ (Fin 1)
    let L : E1 ≃ₗ[ℝ] E1 :=
      (circleInvDiffeo.mfderivToContinuousLinearEquiv (by simp) 1).toLinearEquiv
    have hLv : ∀ v, L v = -v := fun v => mfderiv_circleInv_apply v
    have hL : (L : E1 →ₗ[ℝ] E1) = (-1 : ℝ) • LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      rw [LinearEquiv.coe_coe, hLv, LinearMap.smul_apply, LinearMap.id_apply, neg_smul, one_smul]
    have hdet : LinearMap.det (L : E1 →ₗ[ℝ] E1) < 0 := by
      rw [hL, LinearMap.det_smul, LinearMap.det_id, finrank_euclideanSpace_fin]
      norm_num
    have hcard : Fintype.card (Fin 1) = Module.finrank ℝ E1 := by simp [E1]
    have hneg := (Orientation.map_eq_neg_iff_det_neg (circleOrientation.orientation 1) L
      hcard).mpr hdet
    have h1 : circleInvDiffeo 1 = 1 := inv_one
    have hpos : Orientation.map (Fin 1) L (circleOrientation.orientation 1) =
        circleOrientation.orientation 1 := by
      have h2 := h 1
      rw [h1] at h2
      exact h2
    exact Module.Ray.ne_neg_self (circleOrientation.orientation 1) (hpos.symm.trans hneg)
  · exact h

theorem preservesOrientation_or_opposite {E E' H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold J ∞ N] [PreconnectedSpace M] {n : ℕ} (f : M ≃ₘ⟮I, J⟯ N)
    (oM : ManifoldOrientation I M n) (oN : ManifoldOrientation J N n) :
    f.preservesOrientation oM oN ∨ f.preservesOrientation oM.opposite oN := by
  have hbij : ∀ x, Function.Bijective (mfderiv I J f x) := fun x =>
    (f.mfderivToContinuousLinearEquiv (by simp) x).bijective
  obtain ⟨O, hO⟩ := Manifold.exists_manifoldOrientation_pullback I J oM.dimension_eq f
    f.contMDiff hbij oN
  have hpres : f.preservesOrientation O oN := fun x => by
    have he : (Manifold.differentialEquivOfBijective I J f hbij x).toLinearEquiv =
        (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv :=
      LinearEquiv.ext fun v => rfl
    rw [← he]
    exact hO x
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact Or.inl fun x => (hM.false x).elim
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace I x₀) := by
    rw [Fintype.card_fin]
    exact oM.dimension_eq.symm
  rcases Orientation.eq_or_eq_neg (oM.orientation x₀) (O.orientation x₀) hcard with h | h
  · left
    rw [ManifoldOrientation.eq_of_eq_at oM O x₀ h]
    exact hpres
  · right
    have h' : oM.opposite.orientation x₀ = O.orientation x₀ := by
      rw [ManifoldOrientation.opposite_orientation, h]
      exact neg_neg (O.orientation x₀)
    rw [ManifoldOrientation.eq_of_eq_at oM.opposite O x₀ h']
    exact hpres

end Orientation

namespace FibreCoordinate

variable {F : CircleFibration C U} {V : TopologicalSpace.Opens F.base.Carrier}

theorem conjMap_preservesOrientation
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) V 2) :
    ((Diffeomorph.refl (SurfaceModel.model F.base.kind) V ∞).prodCongr
      circleInvDiffeo).preservesOrientation (CircleFibration.productOrientation F V o)
      (CircleFibration.productOrientation F V o).opposite := by
  have h := Diffeomorph.prodCongr_preservesOrientation (by norm_num) le_rfl
    (Diffeomorph.refl (SurfaceModel.model F.base.kind) V ∞) circleInvDiffeo
    (Diffeomorph.preservesOrientation_refl o) circleInvDiffeo_preservesOrientation
  unfold CircleFibration.productOrientation
  rw [productOrientation_opposite_right]
  exact h

theorem connectedSpace_comap [ConnectedSpace V] (τ : FibreCoordinate F V) :
    ConnectedSpace (TopologicalSpace.Opens.comap F.projection V) :=
  τ.toDiffeo.symm.surjective.connectedSpace τ.toDiffeo.symm.continuous

theorem exists_isPositive [ConnectedSpace V] (τ : FibreCoordinate F V)
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) V 2) :
    ∃ τ' : FibreCoordinate F V, τ'.IsPositive o ∧ (τ' = τ ∨ τ' = τ.conj) := by
  have : ConnectedSpace (TopologicalSpace.Opens.comap F.projection V) := τ.connectedSpace_comap
  rcases preservesOrientation_or_opposite τ.toDiffeo (CircleFibration.totalOrientation F V)
    (CircleFibration.productOrientation F V o) with h | h
  · exact ⟨τ, h, Or.inl rfl⟩
  · refine ⟨τ.conj, ?_, Or.inr rfl⟩
    have h1 := Diffeomorph.preservesOrientation_opposite h
    rw [ManifoldOrientation.opposite_opposite] at h1
    have h2 := Diffeomorph.preservesOrientation_opposite (conjMap_preservesOrientation o)
    rw [ManifoldOrientation.opposite_opposite] at h2
    exact Diffeomorph.preservesOrientation_trans h1 h2

end FibreCoordinate

section Locality

variable {F : CircleFibration C U} {V W : TopologicalSpace.Opens F.base.Carrier}

def CircleFibration.baseProductOrientation (F : CircleFibration C U)
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2) :
    ManifoldOrientation ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      (F.base.Carrier × Circle) 3 :=
  DifferentialGeometry.productOrientation (SurfaceModel.model F.base.kind) (𝓡 1) (by norm_num)
    le_rfl o circleOrientation

theorem CircleFibration.productOrientation_restrictOpen (F : CircleFibration C U)
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
    (V : TopologicalSpace.Opens F.base.Carrier) (q : V × Circle) :
    (CircleFibration.productOrientation F V (o.restrictOpen V)).orientation q =
      (CircleFibration.baseProductOrientation F o).orientation (q.1.val, q.2) := by
  have hc2 : Fintype.card (Fin 2) =
      Module.finrank ℝ (TangentSpace (SurfaceModel.model F.base.kind) q.1.val) := by
    rw [Fintype.card_fin]
    exact o.dimension_eq.symm
  have hc1 : Fintype.card (Fin 1) = Module.finrank ℝ (TangentSpace (𝓡 1) q.2) := by
    rw [Fintype.card_fin]
    exact circleOrientation.dimension_eq.symm
  let bd := basisOfOrientation inferInstance ⟨⟨0, by norm_num⟩⟩ (o.orientation q.1.val) hc2
  let cd := basisOfOrientation inferInstance ⟨⟨0, by norm_num⟩⟩
    (circleOrientation.orientation q.2) hc1
  have h1 := productOrientation_characterization (SurfaceModel.model F.base.kind) (𝓡 1)
    (by norm_num) le_rfl o circleOrientation q.1.val q.2 bd.1 cd.1 bd.2 cd.2
  have h2 := productOrientation_characterization (SurfaceModel.model F.base.kind) (𝓡 1)
    (by norm_num) le_rfl (o.restrictOpen V) circleOrientation q.1 q.2 bd.1 cd.1 bd.2 cd.2
  exact h2.symm.trans h1

theorem FibreCoordinate.mfderiv_toDiffeo_apply (τ : FibreCoordinate F V)
    (x : TopologicalSpace.Opens.comap F.projection V) (v : EuclideanSpace ℝ (Fin 3)) :
    mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1)) τ.toDiffeo x v =
      mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1))
        (fun y : U => (F.projection y, τ.angle y)) x.val v := by
  have hval : MDifferentiableAt (SurfaceModel.model F.base.kind) (SurfaceModel.model F.base.kind)
      (Subtype.val : V → F.base.Carrier) (τ.toDiffeo x).1 :=
    ((contMDiff_subtype_val (I := SurfaceModel.model F.base.kind) (U := V)
      (n := ∞)).mdifferentiable (by simp)) _
  have hid : MDifferentiableAt (𝓡 1) (𝓡 1) (id : Circle → Circle) (τ.toDiffeo x).2 :=
    mdifferentiableAt_id
  have hg : MDifferentiableAt ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      (Prod.map (Subtype.val : V → F.base.Carrier) (id : Circle → Circle)) (τ.toDiffeo x) :=
    hval.prodMap hid
  have hτ : MDifferentiableAt C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      τ.toDiffeo x := (τ.toDiffeo.contMDiff.mdifferentiable (by simp)) x
  have hcomp : Prod.map (Subtype.val : V → F.base.Carrier) (id : Circle → Circle) ∘ τ.toDiffeo =
      fun y : TopologicalSpace.Opens.comap F.projection V => (F.projection y.val, τ.angle y.val) :=
    funext fun y => by
      rw [Function.comp_apply, τ.toDiffeo_apply]
      rfl
  have h1 := mfderiv_comp_apply x hg hτ v
  rw [hcomp, mfderiv_prodMap hval hid, mfderiv_subtype_val, mfderiv_id,
    DifferentialGeometry.mfderiv_restrict_open (fun y : U => (F.projection y, τ.angle y))
      (TopologicalSpace.Opens.comap F.projection V) x] at h1
  exact h1.symm

theorem FibreCoordinate.isPositive_of_local
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
    (τ : FibreCoordinate F V)
    (h : ∀ x : U, F.projection x ∈ V → ∃ (W : TopologicalSpace.Opens F.base.Carrier)
      (τ' : FibreCoordinate F W), F.projection x ∈ W ∧ τ'.IsPositive (o.restrictOpen W) ∧
        τ.angle =ᶠ[𝓝 x] τ'.angle) :
    τ.IsPositive (o.restrictOpen V) := by
  intro x
  obtain ⟨W, τ', hxW, hpos, heq⟩ := h x.val x.2
  let x' : TopologicalSpace.Opens.comap F.projection W := ⟨x.val, hxW⟩
  have hx' := hpos x'
  have hL : ((τ.toDiffeo.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv :
      EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) =
      ((τ'.toDiffeo.mfderivToContinuousLinearEquiv (by simp) x').toLinearEquiv :
        EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) := by
    apply LinearEquiv.ext
    intro v
    change mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1)) τ.toDiffeo x v =
      mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1)) τ'.toDiffeo x' v
    rw [τ.mfderiv_toDiffeo_apply x v, τ'.mfderiv_toDiffeo_apply x' v]
    have hamb : (fun y : U => (F.projection y, τ.angle y)) =ᶠ[𝓝 x.val]
        (fun y : U => (F.projection y, τ'.angle y)) :=
      heq.mono fun y hy => congrArg (Prod.mk (F.projection y)) hy
    rw [hamb.mfderiv_eq]
    rfl
  have hpt : (((τ.toDiffeo x).1.val, (τ.toDiffeo x).2) : F.base.Carrier × Circle) =
      ((τ'.toDiffeo x').1.val, (τ'.toDiffeo x').2) := by
    refine Prod.ext ((τ.fst_eq x).trans (τ'.fst_eq x').symm) ?_
    change (τ.toDiffeo x).2 = (τ'.toDiffeo x').2
    rw [← τ.angle_of_mem x.val x.2, ← τ'.angle_of_mem x'.val x'.2]
    exact heq.eq_of_nhds
  have hP : (CircleFibration.productOrientation F V (o.restrictOpen V)).orientation
      (τ.toDiffeo x) = (CircleFibration.productOrientation F W (o.restrictOpen W)).orientation
        (τ'.toDiffeo x') := by
    rw [CircleFibration.productOrientation_restrictOpen F o V (τ.toDiffeo x),
      CircleFibration.productOrientation_restrictOpen F o W (τ'.toDiffeo x'), hpt]
  change Orientation.map (Fin 3) ((τ.toDiffeo.mfderivToContinuousLinearEquiv (by simp)
    x).toLinearEquiv) ((C.orientation.restrictOpen U).orientation x.val) = _
  rw [hL, hP]
  exact hx'

theorem FibreCoordinate.IsPositive.restrict
    {o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2}
    {τ : FibreCoordinate F V} (hτ : τ.IsPositive (o.restrictOpen V)) (hWV : W ≤ V) :
    (τ.restrict hWV).IsPositive (o.restrictOpen W) := by
  refine (τ.restrict hWV).isPositive_of_local o fun x hx => ⟨V, τ, hWV hx, hτ, ?_⟩
  filter_upwards [(FibreCoordinate.isOpen_preimage W).mem_nhds hx] with y hy
  exact τ.angle_restrict hWV y hy

end Locality


section ParametricInverse

def halfPlaneFlip (p : EuclideanSpace ℝ (Fin 2) × ℝ) : (ℝ × ℝ) × ℝ := ((p.1 1, p.2), p.1 0)

def halfPlaneUnflip (q : (ℝ × ℝ) × ℝ) : EuclideanSpace ℝ (Fin 2) × ℝ :=
  (q.2 • EuclideanSpace.single 0 1 + q.1.1 • EuclideanSpace.single 1 1, q.1.2)

theorem contDiff_euclidean_apply (i : Fin 2) :
    ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 2) => y i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

theorem contDiff_halfPlaneFlip : ContDiff ℝ ∞ halfPlaneFlip :=
  (((contDiff_euclidean_apply 1).comp contDiff_fst).prodMk contDiff_snd).prodMk
    ((contDiff_euclidean_apply 0).comp contDiff_fst)

theorem contDiff_halfPlaneUnflip : ContDiff ℝ ∞ halfPlaneUnflip :=
  ((contDiff_snd.smul contDiff_const).add
    ((contDiff_fst.comp contDiff_fst).smul contDiff_const)).prodMk
    (contDiff_snd.comp contDiff_fst)

theorem halfPlaneUnflip_flip (p : EuclideanSpace ℝ (Fin 2) × ℝ) :
    halfPlaneUnflip (halfPlaneFlip p) = p := by
  refine Prod.ext ?_ rfl
  ext i
  fin_cases i <;> simp [halfPlaneUnflip, halfPlaneFlip]

theorem halfPlaneUnflip_fst_zero (q : (ℝ × ℝ) × ℝ) : (halfPlaneUnflip q).1 0 = q.2 := by
  simp [halfPlaneUnflip]

theorem exists_extension_halfPlane {f : EuclideanSpace ℝ (Fin 2) × ℝ → ℝ}
    {N : Set (EuclideanSpace ℝ (Fin 2) × ℝ)} (hN : IsOpen N) {p₀ : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hp₀ : p₀ ∈ N) (hp₀r : 0 ≤ p₀.1 0) (hf : ContDiffOn ℝ ∞ f (N ∩ {p | 0 ≤ p.1 0})) :
    ∃ N' : Set (EuclideanSpace ℝ (Fin 2) × ℝ), IsOpen N' ∧ p₀ ∈ N' ∧ N' ⊆ N ∧
      ∃ g : EuclideanSpace ℝ (Fin 2) × ℝ → ℝ, ContDiffOn ℝ ∞ g N' ∧
        EqOn g f (N' ∩ {p | 0 ≤ p.1 0}) := by
  have hcont0 : Continuous fun p : EuclideanSpace ℝ (Fin 2) × ℝ => p.1 0 :=
    (contDiff_euclidean_apply 0).continuous.comp continuous_fst
  rcases eq_or_lt_of_le hp₀r with h0 | hpos
  · let U' := halfPlaneUnflip ⁻¹' N
    have hU' : IsOpen U' := hN.preimage contDiff_halfPlaneUnflip.continuous
    have hq : ((p₀.1 1, p₀.2), (0 : ℝ)) ∈ U' := by
      change halfPlaneUnflip ((p₀.1 1, p₀.2), 0) ∈ N
      have h := halfPlaneUnflip_flip p₀
      rw [halfPlaneFlip, ← h0] at h
      rw [h]
      exact hp₀
    have hf' : ContDiffOn ℝ ∞ (f ∘ halfPlaneUnflip) (U' ∩ (univ ×ˢ Ici (0 : ℝ))) := by
      refine hf.comp contDiff_halfPlaneUnflip.contDiffOn fun q hq => ⟨hq.1, ?_⟩
      change 0 ≤ (halfPlaneUnflip q).1 0
      rw [halfPlaneUnflip_fst_zero]
      exact hq.2.2
    obtain ⟨V', hV', hqV', hV'U', g', hg', heq'⟩ :=
      DifferentialGeometry.Analysis.exists_contDiffOn_extension_across_halfSpace_boundary hU' hq hf'
    refine ⟨halfPlaneFlip ⁻¹' V', hV'.preimage contDiff_halfPlaneFlip.continuous, ?_, ?_,
      g' ∘ halfPlaneFlip, hg'.comp contDiff_halfPlaneFlip.contDiffOn fun p hp => hp, ?_⟩
    · change halfPlaneFlip p₀ ∈ V'
      rw [halfPlaneFlip, ← h0]
      exact hqV'
    · intro p hp
      have h := hV'U' hp
      change halfPlaneUnflip (halfPlaneFlip p) ∈ N at h
      rwa [halfPlaneUnflip_flip] at h
    · intro p hp
      have h := heq' ⟨hp.1, mem_univ _, (show 0 ≤ (halfPlaneFlip p).2 from hp.2)⟩
      simp only [Function.comp_apply] at h ⊢
      rw [h, halfPlaneUnflip_flip]
  · refine ⟨N ∩ {p | 0 < p.1 0}, hN.inter (isOpen_lt continuous_const hcont0), ⟨hp₀, hpos⟩,
      inter_subset_left, f,
      hf.mono fun p hp => ⟨hp.1, show 0 ≤ p.1 0 from (show 0 < p.1 0 from hp.2).le⟩,
      fun p _ => rfl⟩


theorem exists_extension_surfaceModel (k : SurfaceModel) {f : EuclideanSpace ℝ (Fin 2) × ℝ → ℝ}
    {N : Set (EuclideanSpace ℝ (Fin 2) × ℝ)} (hN : IsOpen N) {p₀ : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hp₀ : p₀ ∈ N) (hp₀r : p₀.1 ∈ range (SurfaceModel.model k))
    (hf : ContDiffOn ℝ ∞ f (N ∩ (range (SurfaceModel.model k) ×ˢ univ))) :
    ∃ N' : Set (EuclideanSpace ℝ (Fin 2) × ℝ), IsOpen N' ∧ p₀ ∈ N' ∧ N' ⊆ N ∧
      ∃ g : EuclideanSpace ℝ (Fin 2) × ℝ → ℝ, ContDiffOn ℝ ∞ g N' ∧
        EqOn g f (N' ∩ (range (SurfaceModel.model k) ×ˢ univ)) := by
  cases k with
  | closed =>
    have hr : range (SurfaceModel.model ModelBoundaryKind.closed) = univ :=
      eq_univ_of_forall fun y => ⟨y, rfl⟩
    rw [hr] at hf ⊢
    exact ⟨N, hN, hp₀, subset_rfl, f, hf.mono fun q hq => ⟨hq, mem_univ _, mem_univ _⟩,
      fun _ _ => rfl⟩
  | withBoundary =>
    have hr : range (SurfaceModel.model ModelBoundaryKind.withBoundary) ×ˢ (univ : Set ℝ) =
        {p : EuclideanSpace ℝ (Fin 2) × ℝ | 0 ≤ p.1 0} := by
      ext q
      change q.1 ∈ range (𝓡∂ 2) ∧ q.2 ∈ univ ↔ _
      rw [range_modelWithCornersEuclideanHalfSpace]
      simp
    have hp₀' : 0 ≤ p₀.1 0 := by
      have h : (p₀.1, (0 : ℝ)) ∈ range (SurfaceModel.model ModelBoundaryKind.withBoundary) ×ˢ
          (univ : Set ℝ) := ⟨hp₀r, mem_univ _⟩
      rw [hr] at h
      exact h
    rw [hr] at hf ⊢
    exact exists_extension_halfPlane hN hp₀ hp₀' hf

theorem contMDiffOn_inverse_param {k : SurfaceModel} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (SurfaceModel.Space k) X] [IsManifold (SurfaceModel.model k) ∞ X]
    {W : Set X} (hW : IsOpen W) {G R : X × ℝ → ℝ}
    (hG : ContMDiffOn ((SurfaceModel.model k).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ G (W ×ˢ univ))
    (hinj : ∀ b ∈ W, Function.Injective fun t => G (b, t))
    (hderiv : ∀ b ∈ W, ∀ t, deriv (fun t => G (b, t)) t ≠ 0)
    (hR : ∀ b ∈ W, ∀ s, G (b, R (b, s)) = s) :
    ContMDiffOn ((SurfaceModel.model k).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ R (W ×ˢ univ) := by
  rintro ⟨b₀, s₀⟩ ⟨hb₀, -⟩
  set I := SurfaceModel.model k
  set φ := extChartAt I b₀
  set t₀ := R (b₀, s₀)
  let f : EuclideanSpace ℝ (Fin 2) × ℝ → ℝ := fun q => G (φ.symm q.1, q.2)
  have hψ : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => (φ.symm q.1, q.2)) (φ.target ×ˢ univ) :=
    ((contMDiffOn_extChartAt_symm b₀).comp contDiff_fst.contMDiff.contMDiffOn
      fun q hq => hq.1).prodMk contDiff_snd.contMDiff.contMDiffOn
  have hfsm : ContDiffOn ℝ ∞ f ((φ.target ∩ φ.symm ⁻¹' W) ×ˢ univ) := by
    refine contMDiffOn_iff_contDiffOn.mp ?_
    exact hG.comp (hψ.mono fun q hq => ⟨hq.1.1, hq.2⟩) fun q hq => ⟨hq.1.2, mem_univ _⟩
  have hT : φ.target ∩ φ.symm ⁻¹' W ∈ 𝓝[range I] (φ b₀) := by
    rw [← nhdsWithin_extChartAt_target_eq]
    refine Filter.inter_mem self_mem_nhdsWithin ?_
    refine (continuousOn_extChartAt_symm b₀ _ (mem_extChartAt_target b₀)).preimage_mem_nhdsWithin
      (hW.mem_nhds ?_)
    rw [extChartAt_to_inv]
    exact hb₀
  obtain ⟨U₁, hU₁, hy₀U₁, hU₁sub⟩ := mem_nhdsWithin.mp hT
  have hy₀r : φ b₀ ∈ range I := extChartAt_target_subset_range b₀ (mem_extChartAt_target b₀)
  have hfN : ContDiffOn ℝ ∞ f ((U₁ ×ˢ univ) ∩ (range I ×ˢ univ)) :=
    hfsm.mono fun q hq => ⟨hU₁sub ⟨hq.1.1, hq.2.1⟩, mem_univ _⟩
  obtain ⟨N', hN', hpN', -, h, hh, hheq⟩ := exists_extension_surfaceModel k
    (hU₁.prod isOpen_univ) (p₀ := (φ b₀, t₀)) ⟨hy₀U₁, mem_univ _⟩ hy₀r hfN
  have hslice : (fun t => h (φ b₀, t)) =ᶠ[𝓝 t₀] fun t => G (b₀, t) := by
    have hc : ContinuousAt (fun t : ℝ => (φ b₀, t)) t₀ :=
      continuousAt_const.prodMk continuousAt_id
    filter_upwards [hc.preimage_mem_nhds (hN'.mem_nhds hpN')] with t ht
    rw [hheq ⟨ht, hy₀r, mem_univ _⟩]
    change G (φ.symm (φ b₀), t) = G (b₀, t)
    rw [extChartAt_to_inv]
  have hdiff : DifferentiableAt ℝ h (φ b₀, t₀) :=
    (hh.contDiffAt (hN'.mem_nhds hpN')).differentiableAt (by simp)
  have hvert : fderiv ℝ h (φ b₀, t₀) (0, 1) ≠ 0 := by
    have hd : HasDerivAt (fun t => h (φ b₀, t)) (fderiv ℝ h (φ b₀, t₀) (0, 1)) t₀ :=
      hdiff.hasFDerivAt.comp_hasDerivAt t₀ ((hasDerivAt_const t₀ (φ b₀)).prodMk
        (hasDerivAt_id t₀))
    rw [← hd.deriv, hslice.deriv_eq]
    exact hderiv b₀ hb₀ t₀
  obtain ⟨e, hpe, hesub, -, heinv, he, hparam⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_preserving_parameter hh hN' hpN' hvert
  have hs₀ : h (φ b₀, t₀) = s₀ := by
    rw [hheq ⟨hpN', hy₀r, mem_univ _⟩]
    change G (φ.symm (φ b₀), t₀) = s₀
    rw [extChartAt_to_inv]
    exact hR b₀ hb₀ s₀
  have htarget : (φ b₀, s₀) ∈ e.target := by
    have h1 := e.map_source hpe
    rw [he] at h1
    simp only at h1
    rwa [hs₀] at h1
  have hev : R =ᶠ[𝓝 (b₀, s₀)] fun p : X × ℝ => (e.symm (φ p.1, p.2)).2 := by
    have hc : ContinuousAt (fun p : X × ℝ => (φ p.1, p.2)) (b₀, s₀) :=
      (ContinuousAt.comp (x := (b₀, s₀)) (continuousAt_extChartAt (I := I) b₀)
        continuousAt_fst).prodMk continuousAt_snd
    have h2 : ∀ᶠ p in 𝓝 (b₀, s₀), p.1 ∈ φ.source :=
      continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_source b₀).mem_nhds
        (mem_extChartAt_source b₀))
    filter_upwards [hc.preimage_mem_nhds (e.open_target.mem_nhds htarget), h2,
      continuousAt_fst.preimage_mem_nhds (hW.mem_nhds hb₀)] with p hp1 hp2 hp3
    obtain ⟨hq1, hq2⟩ := hparam _ hp1
    have hsrc : e.symm (φ p.1, p.2) ∈ e.source := e.map_target hp1
    have hr1 : (e.symm (φ p.1, p.2)).1 ∈ range I := by
      rw [hq1]
      exact extChartAt_target_subset_range b₀ (φ.map_source hp2)
    have hfe := hheq ⟨hesub hsrc, hr1, mem_univ _⟩
    have hq1' : (e.symm (φ p.1, p.2)).1 = φ p.1 := hq1
    have hfG : f (e.symm (φ p.1, p.2)) = G (p.1, (e.symm (φ p.1, p.2)).2) := by
      change G (φ.symm (e.symm (φ p.1, p.2)).1, (e.symm (φ p.1, p.2)).2) = _
      rw [hq1', φ.left_inv hp2]
    have hG1 : G (p.1, (e.symm (φ p.1, p.2)).2) = p.2 := by
      rw [← hfG, ← hfe]
      exact hq2
    exact (hinj p.1 hp3 (hG1.trans (hR p.1 hp3 p.2).symm)).symm
  have hinner : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
      (fun p : X × ℝ => (φ p.1, p.2)) (b₀, s₀) :=
    ((contMDiffAt_extChartAt (I := I) (x := b₀)).comp (b₀, s₀) contMDiffAt_fst).prodMk_space
      contMDiffAt_snd
  have houter : ContDiffAt ℝ ∞ (fun q => (e.symm q).2) (φ b₀, s₀) :=
    (heinv.contDiffAt (e.open_target.mem_nhds htarget)).snd
  exact ((ContDiffAt.comp_contMDiffAt (f := fun p : X × ℝ => (φ p.1, p.2)) (x := (b₀, s₀))
    houter hinner).congr_of_eventuallyEq hev).contMDiffWithinAt

end ParametricInverse

section FibreOrientation

open AnnulusStraightening

theorem tangentChartEquiv_real_apply (p y : ℝ)
    (h : y ∈ (trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ)) p).baseSet)
    (v : TangentSpace 𝓘(ℝ, ℝ) y) : tangentChartEquiv 𝓘(ℝ, ℝ) ℝ p y h v = v := by
  rw [tangentChartEquiv, Bundle.Trivialization.linearEquivAt_apply]
  simp
  rfl

def realLineOrientation : ManifoldOrientation 𝓘(ℝ, ℝ) ℝ 1 where
  dimension_eq := Module.finrank_self ℝ
  orientation _ := (Module.Basis.singleton (Fin 1) ℝ).orientation
  locally_constant p x hx := by
    refine ⟨univ, isOpen_univ, mem_univ x, fun y _ => by simp, fun y hy => ?_⟩
    have hc : ∀ (z : ℝ) (hz : z ∈ (trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ)) p).baseSet),
        Orientation.map (Fin 1) (tangentChartEquiv 𝓘(ℝ, ℝ) ℝ p z hz)
          (Module.Basis.singleton (Fin 1) ℝ).orientation =
          (Module.Basis.singleton (Fin 1) ℝ).orientation := by
      intro z hz
      have he : tangentChartEquiv 𝓘(ℝ, ℝ) ℝ p z hz = LinearEquiv.refl ℝ ℝ :=
        LinearEquiv.ext fun v => tangentChartEquiv_real_apply p z hz v
      rw [he]
      erw [Orientation.map_refl]
      rfl
    exact (hc _ _).trans (hc _ _).symm

theorem bijective_mfderiv_cexp (t : ℝ) :
    Function.Bijective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) cexp t) := by
  obtain ⟨e, he⟩ := (isLocalDiffeomorph_cexp t).isInvertible_mfderiv (by simp)
  rw [← he]
  exact e.bijective

def cexpDeriv (t : ℝ) : ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (Manifold.differentialEquivOfBijective 𝓘(ℝ, ℝ) (𝓡 1) cexp bijective_mfderiv_cexp t).toLinearEquiv

theorem cexpDeriv_apply (t v : ℝ) : cexpDeriv t v = mfderiv 𝓘(ℝ, ℝ) (𝓡 1) cexp t v :=
  rfl

theorem exists_cexp_pullback (oc : ManifoldOrientation (𝓡 1) Circle 1) :
    ∃ s : Orientation ℝ ℝ (Fin 1), ∀ t : ℝ,
      Orientation.map (Fin 1) (cexpDeriv t) s = oc.orientation (cexp t) := by
  obtain ⟨O, hO⟩ := Manifold.exists_manifoldOrientation_pullback (I := 𝓘(ℝ, ℝ)) (J := 𝓡 1)
    (Module.finrank_self ℝ) cexp contMDiff_cexp bijective_mfderiv_cexp oc
  have hcard : Fintype.card (Fin 1) = Module.finrank ℝ (TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ)) := by
    rw [Fintype.card_fin]
    exact (Module.finrank_self ℝ).symm
  rcases Orientation.eq_or_eq_neg (O.orientation 0) (realLineOrientation.orientation 0)
    hcard with h | h
  · refine ⟨realLineOrientation.orientation 0, fun t => ?_⟩
    rw [← hO t, ManifoldOrientation.eq_of_eq_at O realLineOrientation 0 h]
    rfl
  · refine ⟨-realLineOrientation.orientation 0, fun t => ?_⟩
    have h' : O.orientation 0 = realLineOrientation.opposite.orientation 0 := by
      rw [ManifoldOrientation.opposite_orientation]
      exact h
    rw [← hO t, ManifoldOrientation.eq_of_eq_at O realLineOrientation.opposite 0 h']
    rfl

theorem orientation_map_smul_pos {s : Orientation ℝ ℝ (Fin 1)} {a : ℝ} (ha : 0 < a) :
    Orientation.map (Fin 1) (LinearEquiv.smulOfNeZero ℝ ℝ a ha.ne') s = s := by
  refine (Orientation.map_eq_iff_det_pos s _ (by simp)).mpr ?_
  have h : ((LinearEquiv.smulOfNeZero ℝ ℝ a ha.ne' : ℝ ≃ₗ[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) =
      a • LinearMap.id := LinearMap.ext fun v => rfl
  rw [h, LinearMap.det_smul, LinearMap.det_id, Module.finrank_self, pow_one, mul_one]
  exact ha

theorem cexp_lift_mfderiv {g : Circle → Circle} {G : ℝ → ℝ} {t₀ G' : ℝ}
    (hg : MDifferentiableAt (𝓡 1) (𝓡 1) g (cexp t₀)) (hG : HasDerivAt G G' t₀)
    (hlift : (fun t => g (cexp t)) =ᶠ[𝓝 t₀] fun t => cexp (G t)) (v : ℝ) :
    mfderiv (𝓡 1) (𝓡 1) g (cexp t₀) (cexpDeriv t₀ v) = cexpDeriv (G t₀) (G' * v) := by
  have hcexp : ∀ t, MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) cexp t :=
    fun t => (contMDiff_cexp.mdifferentiable (by simp)) t
  have hGm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) G t₀ := hG.differentiableAt.mdifferentiableAt
  have hGd : ∀ v : ℝ, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) G t₀ v = v * G' := by
    intro v
    rw [hG.hasFDerivAt.hasMFDerivAt.mfderiv]
    rfl
  rw [cexpDeriv_apply, cexpDeriv_apply]
  have h1 := mfderiv_comp_apply t₀ hg (hcexp t₀) v
  have h2 := mfderiv_comp_apply t₀ (hcexp (G t₀)) hGm v
  have h3 := hlift.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 1)
  rw [hGd, mul_comm] at h2
  rw [← h2, ← h1]
  exact congrFun (congrArg DFunLike.coe h3) v

theorem orientation_map_of_cexp_lift (oc : ManifoldOrientation (𝓡 1) Circle 1)
    {g : Circle → Circle} {G : ℝ → ℝ} {t₀ G' : ℝ}
    (hg : MDifferentiableAt (𝓡 1) (𝓡 1) g (cexp t₀)) (hG : HasDerivAt G G' t₀) (hpos : 0 < G')
    (hlift : (fun t => g (cexp t)) =ᶠ[𝓝 t₀] fun t => cexp (G t))
    (A : EuclideanSpace ℝ (Fin 1) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1))
    (hA : ∀ v, A v = mfderiv (𝓡 1) (𝓡 1) g (cexp t₀) v) :
    Orientation.map (Fin 1) A (oc.orientation (cexp t₀)) = oc.orientation (cexp (G t₀)) := by
  obtain ⟨s, hs⟩ := exists_cexp_pullback oc
  have heq : (cexpDeriv t₀).trans A =
      (LinearEquiv.smulOfNeZero ℝ ℝ G' hpos.ne').trans (cexpDeriv (G t₀)) :=
    LinearEquiv.ext fun v => by
      change A (cexpDeriv t₀ v) = cexpDeriv (G t₀) (G' • v)
      rw [hA, cexp_lift_mfderiv hg hG hlift, smul_eq_mul]
  rw [← hs t₀, ← orientation_map_trans_fin, heq, orientation_map_trans_fin,
    orientation_map_smul_pos hpos, hs]

theorem orientation_map_smul_neg {s : Orientation ℝ ℝ (Fin 1)} {a : ℝ} (ha : a < 0) :
    Orientation.map (Fin 1) (LinearEquiv.smulOfNeZero ℝ ℝ a ha.ne) s = -s := by
  refine (Orientation.map_eq_neg_iff_det_neg s _ (by simp)).mpr ?_
  have h : ((LinearEquiv.smulOfNeZero ℝ ℝ a ha.ne : ℝ ≃ₗ[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) =
      a • LinearMap.id := LinearMap.ext fun v => rfl
  rw [h, LinearMap.det_smul, LinearMap.det_id, Module.finrank_self, pow_one, mul_one]
  exact ha

theorem orientation_map_of_cexp_lift_neg (oc : ManifoldOrientation (𝓡 1) Circle 1)
    {g : Circle → Circle} {G : ℝ → ℝ} {t₀ G' : ℝ}
    (hg : MDifferentiableAt (𝓡 1) (𝓡 1) g (cexp t₀)) (hG : HasDerivAt G G' t₀) (hneg : G' < 0)
    (hlift : (fun t => g (cexp t)) =ᶠ[𝓝 t₀] fun t => cexp (G t))
    (A : EuclideanSpace ℝ (Fin 1) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1))
    (hA : ∀ v, A v = mfderiv (𝓡 1) (𝓡 1) g (cexp t₀) v) :
    Orientation.map (Fin 1) A (oc.orientation (cexp t₀)) =
      oc.opposite.orientation (cexp (G t₀)) := by
  obtain ⟨s, hs⟩ := exists_cexp_pullback oc
  have heq : (cexpDeriv t₀).trans A =
      (LinearEquiv.smulOfNeZero ℝ ℝ G' hneg.ne).trans (cexpDeriv (G t₀)) :=
    LinearEquiv.ext fun v => by
      change A (cexpDeriv t₀ v) = cexpDeriv (G t₀) (G' • v)
      rw [hA, cexp_lift_mfderiv hg hG hlift, smul_eq_mul]
  rw [ManifoldOrientation.opposite_orientation, ← hs t₀, ← orientation_map_trans_fin, heq,
    orientation_map_trans_fin, orientation_map_smul_neg hneg, Orientation.map_neg, hs]
  rfl

theorem orientation_map_eq_of_shear {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] {n : ℕ} (x : Orientation ℝ M (Fin n))
    (hn : Fintype.card (Fin n) = Module.finrank ℝ M) (S : M ≃ₗ[ℝ] M)
    (hS : ∀ v, S (S v - v) - (S v - v) = 0) : Orientation.map (Fin n) S x = x := by
  refine (Orientation.map_eq_iff_det_pos x S hn).mpr ?_
  let T : M →ₗ[ℝ] M := LinearMap.id + (1 / 2 : ℝ) • ((S : M →ₗ[ℝ] M) - LinearMap.id)
  have hT : T ∘ₗ T = (S : M →ₗ[ℝ] M) := by
    refine LinearMap.ext fun v => ?_
    have h := sub_eq_zero.mp (hS v)
    simp only [T, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
      LinearMap.smul_apply, LinearMap.sub_apply, LinearEquiv.coe_coe, map_add, map_smul,
      map_sub] at h ⊢
    linear_combination (norm := module) (1 / 4 : ℝ) • h
  have hne : LinearMap.det (S : M →ₗ[ℝ] M) ≠ 0 := S.isUnit_det'.ne_zero
  rw [← hT, LinearMap.det_comp] at hne ⊢
  exact lt_of_le_of_ne (mul_self_nonneg _) (Ne.symm hne)

theorem orientation_map_prodCongr_right {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (o : ManifoldOrientation I M 2) (oc oc' : ManifoldOrientation (𝓡 1) Circle 1) (b : M)
    (z z' : Circle) (A : TangentSpace (𝓡 1) z ≃ₗ[ℝ] TangentSpace (𝓡 1) z')
    (hA : Orientation.map (Fin 1) A (oc.orientation z) = oc'.orientation z') :
    Orientation.map (Fin (2 + 1)) ((LinearEquiv.refl ℝ (TangentSpace I b)).prodCongr A)
      ((DifferentialGeometry.productOrientation I (𝓡 1) (by norm_num) le_rfl o oc).orientation
        (b, z)) =
      (DifferentialGeometry.productOrientation I (𝓡 1) (by norm_num) le_rfl o oc').orientation
        (b, z') := by
  have hc2 : Fintype.card (Fin 2) = Module.finrank ℝ (TangentSpace I b) := by
    rw [Fintype.card_fin]
    exact o.dimension_eq.symm
  have hc1 : Fintype.card (Fin 1) = Module.finrank ℝ (TangentSpace (𝓡 1) z) := by
    rw [Fintype.card_fin]
    exact oc.dimension_eq.symm
  let bd := basisOfOrientation inferInstance ⟨⟨0, by norm_num⟩⟩ (o.orientation b) hc2
  let cd := basisOfOrientation inferInstance ⟨⟨0, by norm_num⟩⟩ (oc.orientation z) hc1
  rw [← productOrientation_characterization I (𝓡 1) (by norm_num) le_rfl o oc b z bd.1 cd.1
    bd.2 cd.2, productTangentBasis_orientation_map bd.1 cd.1 (LinearEquiv.refl ℝ _) A]
  have hb : bd.1.map (LinearEquiv.refl ℝ (TangentSpace I b)) = bd.1 :=
    Module.Basis.eq_of_apply_eq fun i => rfl
  refine productOrientation_characterization I (𝓡 1) (by norm_num) le_rfl o oc' b z' _ _
    (by rw [hb]; exact bd.2) ?_
  rw [Module.Basis.orientation_map, cd.2, hA]

theorem orientation_map_fibrewise {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (o : ManifoldOrientation I M 2) (oc oc' : ManifoldOrientation (𝓡 1) Circle 1) (b : M)
    (z z' : Circle) (A : TangentSpace (𝓡 1) z ≃ₗ[ℝ] TangentSpace (𝓡 1) z')
    (hA : Orientation.map (Fin 1) A (oc.orientation z) = oc'.orientation z')
    (L : (E × EuclideanSpace ℝ (Fin 1)) ≃ₗ[ℝ] (E × EuclideanSpace ℝ (Fin 1)))
    (h1 : ∀ v, (L v).1 = v.1) (h2 : ∀ w, L (0, w) = (0, A w)) :
    Orientation.map (Fin (2 + 1)) L
      ((DifferentialGeometry.productOrientation I (𝓡 1) (by norm_num) le_rfl o oc).orientation
        (b, z)) =
      (DifferentialGeometry.productOrientation I (𝓡 1) (by norm_num) le_rfl o oc').orientation
        (b, z') := by
  let L₀ : (E × EuclideanSpace ℝ (Fin 1)) ≃ₗ[ℝ] (E × EuclideanSpace ℝ (Fin 1)) :=
    (LinearEquiv.refl ℝ E).prodCongr A
  let S := L.trans L₀.symm
  have hL₀s : ∀ w : EuclideanSpace ℝ (Fin 1), L₀.symm (0, A w) = (0, w) := by
    intro w
    apply L₀.injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hS1 : ∀ v, (S v).1 = v.1 := by
    intro v
    change (L₀.symm (L v)).1 = v.1
    rw [← h1 v]
    rfl
  have hS : ∀ v, S (S v - v) - (S v - v) = 0 := by
    intro v
    have hd : S v - v = (0, (S v - v).2) := Prod.ext (by simp [hS1]) rfl
    have hS0 : S (0, (S v - v).2) = (0, (S v - v).2) := by
      change L₀.symm (L (0, (S v - v).2)) = _
      rw [h2]
      exact hL₀s _
    rw [hd, hS0, sub_self]
  have hLS : L = S.trans L₀ := LinearEquiv.ext fun v => by
    change L v = L₀ (L₀.symm (L v))
    rw [LinearEquiv.apply_symm_apply]
  have hcard : Fintype.card (Fin (2 + 1)) =
      Module.finrank ℝ (E × EuclideanSpace ℝ (Fin 1)) := by
    rw [Fintype.card_fin, Module.finrank_prod, finrank_euclideanSpace_fin, o.dimension_eq]
  rw [hLS]
  have e1 := orientation_map_trans_fin S L₀
    ((DifferentialGeometry.productOrientation I (𝓡 1) (by norm_num) le_rfl o oc).orientation
      (b, z))
  have e2 := orientation_map_eq_of_shear
    ((DifferentialGeometry.productOrientation I (𝓡 1) (by norm_num) le_rfl o oc).orientation
      (b, z)) hcard S hS
  exact e1.trans ((congrArg (Orientation.map (Fin (2 + 1)) L₀) e2).trans
    (orientation_map_prodCongr_right o oc oc' b z z' A hA))

end FibreOrientation

section FlowNormalize

open AnnulusStraightening

def collarBump (ε s : ℝ) : ℝ :=
  cutoff (-(ε / 2)) (-(ε / 4)) s * cutoff (-(ε / 2)) (-(ε / 4)) (-s)

def collarShift (ε s : ℝ) : ℝ := s * collarBump ε s

theorem contDiff_collarShift (ε : ℝ) : ContDiff ℝ ∞ (collarShift ε) :=
  contDiff_id.mul ((contDiff_cutoff _ _).mul ((contDiff_cutoff _ _).comp contDiff_neg))

theorem collarBump_nonneg (ε s : ℝ) : 0 ≤ collarBump ε s :=
  mul_nonneg (cutoff_nonneg _ _ _) (cutoff_nonneg _ _ _)

theorem collarBump_le_one (ε s : ℝ) : collarBump ε s ≤ 1 := by
  have h1 := cutoff_le_one (-(ε / 2)) (-(ε / 4)) s
  have h2 := cutoff_le_one (-(ε / 2)) (-(ε / 4)) (-s)
  have h3 := cutoff_nonneg (-(ε / 2)) (-(ε / 4)) s
  have h4 := cutoff_nonneg (-(ε / 2)) (-(ε / 4)) (-s)
  unfold collarBump
  nlinarith

theorem collarShift_of_abs_le {ε s : ℝ} (hε : 0 < ε) (hs : |s| ≤ ε / 4) :
    collarShift ε s = s := by
  have h1 : cutoff (-(ε / 2)) (-(ε / 4)) s = 1 :=
    cutoff_of_ge (by linarith) (by linarith [neg_abs_le s])
  have h2 : cutoff (-(ε / 2)) (-(ε / 4)) (-s) = 1 :=
    cutoff_of_ge (by linarith) (by linarith [le_abs_self s])
  rw [collarShift, collarBump, h1, h2]
  ring

theorem collarShift_of_le_abs {ε s : ℝ} (hε : 0 < ε) (hs : ε / 2 ≤ |s|) :
    collarShift ε s = 0 := by
  rcases le_abs.mp hs with h | h
  · rw [collarShift, collarBump,
      cutoff_of_le (s₁ := -(ε / 2)) (by linarith) (show -s ≤ -(ε / 2) by linarith)]
    ring
  · rw [collarShift, collarBump, cutoff_of_le (s₁ := -(ε / 2)) (by linarith)
      (show s ≤ -(ε / 2) by linarith)]
    ring

theorem abs_sub_collarShift_le (ε s : ℝ) : |s - collarShift ε s| ≤ |s| := by
  have h : s - collarShift ε s = s * (1 - collarBump ε s) := by
    rw [collarShift]
    ring
  have h0 := collarBump_nonneg ε s
  have h1 := collarBump_le_one ε s
  rw [h, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - collarBump ε s)]
  nlinarith [abs_nonneg s]

variable {F : CircleFibration C U} {V : TopologicalSpace.Opens F.base.Carrier}
  {c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
    (Circle × ℝ) F.base.Carrier ∞}

namespace LiftedBicollar

theorem baseFlow_zero (L : LiftedBicollar F c) (b : F.base.Carrier) : L.baseFlow 0 b = b := by
  obtain ⟨x, rfl⟩ := F.surjective b
  rw [← L.projection_flow, L.flow_zero]

theorem flow_neg_flow (L : LiftedBicollar F c) (r : ℝ) (x : U) :
    L.flow (-r) (L.flow r x) = x := by
  rw [← L.flow_add, neg_add_cancel, L.flow_zero]

theorem flow_flow_neg (L : LiftedBicollar F c) (r : ℝ) (x : U) :
    L.flow r (L.flow (-r) x) = x := by
  rw [← L.flow_add, add_neg_cancel, L.flow_zero]

end LiftedBicollar

open scoped Classical in
def collarShiftFn (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
    (Circle × ℝ) F.base.Carrier ∞) (ε : ℝ) (b : F.base.Carrier) : ℝ :=
  if b ∈ c.target then collarShift ε (c.symm b).2 else 0

open scoped Classical in
def collarPull (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
    (Circle × ℝ) F.base.Carrier ∞) (ε : ℝ) (b : F.base.Carrier) : F.base.Carrier :=
  if b ∈ c.target then c ((c.symm b).1, (c.symm b).2 - collarShift ε (c.symm b).2) else b

theorem contMDiff_of_eqOn_compl {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N]
    [ChartedSpace H' N] {f g : F.base.Carrier → N} {K : Set F.base.Carrier} (hK : IsClosed K)
    (hKc : K ⊆ c.target) (hf : ContMDiffOn (SurfaceModel.model F.base.kind) J ∞ f c.target)
    (hg : ContMDiff (SurfaceModel.model F.base.kind) J ∞ g) (hfg : ∀ b ∉ K, f b = g b) :
    ContMDiff (SurfaceModel.model F.base.kind) J ∞ f := by
  intro b
  by_cases hb : b ∈ c.target
  · exact hf.contMDiffAt (c.open_target.mem_nhds hb)
  · have hbK : b ∉ K := fun h => hb (hKc h)
    exact (hg b).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hK.isOpen_compl.mem_nhds hbK) fun y hy => hfg y hy)

def collarCore (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
    (Circle × ℝ) F.base.Carrier ∞) (ε : ℝ) : Set F.base.Carrier :=
  c '' (univ ×ˢ Icc (-(ε / 2)) (ε / 2))

theorem symm_snd_of_not_mem_collarCore {ε : ℝ} (b : F.base.Carrier) (hb : b ∈ c.target)
    (hK : b ∉ collarCore c ε) : ε / 2 < |(c.symm b).2| := by
  by_contra h
  exact hK ⟨c.symm b, ⟨mem_univ _, (abs_le.mp (not_lt.mp h)).1, (abs_le.mp (not_lt.mp h)).2⟩,
    c.toPartialEquiv.right_inv hb⟩

theorem collar_cases {ε : ℝ} (hε : 0 < ε) (b : F.base.Carrier) :
    (collarShiftFn c ε b = 0 ∧ collarPull c ε b = b) ∨
      (b ∈ c.target ∧ |(c.symm b).2| < ε / 2 ∧
        collarShiftFn c ε b = collarShift ε (c.symm b).2 ∧
        collarPull c ε b = c ((c.symm b).1, (c.symm b).2 - collarShift ε (c.symm b).2)) := by
  by_cases hb : b ∈ c.target
  · by_cases hs : ε / 2 ≤ |(c.symm b).2|
    · left
      refine ⟨?_, ?_⟩
      · rw [collarShiftFn, ite_eq_left hb, collarShift_of_le_abs hε hs]
      · rw [collarPull, ite_eq_left hb, collarShift_of_le_abs hε hs, sub_zero]
        exact c.toPartialEquiv.right_inv hb
    · right
      exact ⟨hb, not_le.mp hs, by rw [collarShiftFn, ite_eq_left hb],
        by rw [collarPull, ite_eq_left hb]⟩
  · left
    exact ⟨by rw [collarShiftFn, ite_eq_right hb], by rw [collarPull, ite_eq_right hb]⟩

theorem collarShiftFn_eq_zero {ε : ℝ} (hε : 0 < ε) (b : F.base.Carrier)
    (hb : ∀ θ s, |s| < ε → b ≠ c (θ, s)) : collarShiftFn c ε b = 0 := by
  rcases collar_cases hε b with ⟨h, -⟩ | ⟨hb', hs, -, -⟩
  · exact h
  · exact absurd (c.toPartialEquiv.right_inv hb').symm
      (hb (c.symm b).1 (c.symm b).2 (by linarith))

namespace LiftedBicollar

variable (L : LiftedBicollar F c)

theorem core_subset_target {ε : ℝ} (hε : ε ≤ L.width) : collarCore c ε ⊆ c.target := by
  rintro b ⟨q, hq, rfl⟩
  refine c.map_source (L.mem_source q.1 q.2 ?_)
  have h := abs_le.mpr ⟨hq.2.1, hq.2.2⟩
  linarith [L.width_lt_reach, L.width_pos]

theorem isClosed_core {ε : ℝ} (hε : ε ≤ L.width) : IsClosed (collarCore c ε) := by
  refine IsCompact.isClosed (IsCompact.image_of_continuousOn (isCompact_univ.prod isCompact_Icc)
    (c.contMDiffOn.continuousOn.mono ?_))
  rintro q hq
  refine L.mem_source q.1 q.2 ?_
  have h := abs_le.mpr ⟨hq.2.1, hq.2.2⟩
  linarith [L.width_lt_reach, L.width_pos]

theorem contMDiff_collarShiftFn {ε : ℝ} (hε : 0 < ε) (hεw : ε ≤ L.width) :
    ContMDiff (SurfaceModel.model F.base.kind) 𝓘(ℝ, ℝ) ∞ (collarShiftFn c ε) := by
  refine contMDiff_of_eqOn_compl (L.isClosed_core hεw) (L.core_subset_target hεw) ?_
    (contMDiff_const (c := (0 : ℝ))) fun b hb => ?_
  · have hs : ContMDiffOn (SurfaceModel.model F.base.kind) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ c.symm
        c.target := c.symm.contMDiffOn
    have h : ContMDiffOn (SurfaceModel.model F.base.kind) 𝓘(ℝ, ℝ) ∞
        (fun b => collarShift ε (c.symm b).2) c.target :=
      (contDiff_collarShift ε).contMDiff.comp_contMDiffOn (contMDiff_snd.comp_contMDiffOn hs)
    exact h.congr fun b hb => by rw [collarShiftFn, ite_eq_left hb]
  · by_cases hb' : b ∈ c.target
    · rw [collarShiftFn, ite_eq_left hb',
        collarShift_of_le_abs hε (symm_snd_of_not_mem_collarCore b hb' hb).le]
    · rw [collarShiftFn, ite_eq_right hb']

theorem collarPull_mem_source {ε : ℝ} (hε : 0 < ε) (hεw : ε ≤ L.width) (b : F.base.Carrier)
    (hb : b ∈ c.target) :
    ((c.symm b).1, (c.symm b).2 - collarShift ε (c.symm b).2) ∈ c.source := by
  by_cases hs : ε / 2 ≤ |(c.symm b).2|
  · rw [collarShift_of_le_abs hε hs, sub_zero]
    exact c.toPartialEquiv.map_target hb
  · refine L.mem_source _ _ ?_
    have := abs_sub_collarShift_le ε (c.symm b).2
    linarith [L.width_lt_reach, not_le.mp hs]

theorem contMDiff_collarPull {ε : ℝ} (hε : 0 < ε) (hεw : ε ≤ L.width) :
    ContMDiff (SurfaceModel.model F.base.kind) (SurfaceModel.model F.base.kind) ∞
      (collarPull c ε) := by
  refine contMDiff_of_eqOn_compl (L.isClosed_core hεw) (L.core_subset_target hεw) ?_
    contMDiff_id fun b hb => ?_
  · have hs : ContMDiffOn (SurfaceModel.model F.base.kind) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ c.symm
        c.target := c.symm.contMDiffOn
    have hin : ContMDiffOn (SurfaceModel.model F.base.kind) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
        (fun b => ((c.symm b).1, (c.symm b).2 - collarShift ε (c.symm b).2)) c.target :=
      (contMDiff_fst.comp_contMDiffOn hs).prodMk
        (((contDiff_id.sub (contDiff_collarShift ε)).contMDiff).comp_contMDiffOn
          (contMDiff_snd.comp_contMDiffOn hs))
    have h := c.contMDiffOn.comp hin fun b hb => L.collarPull_mem_source hε hεw b hb
    exact h.congr fun b hb => by rw [collarPull, ite_eq_left hb]; rfl
  · by_cases hb' : b ∈ c.target
    · rw [collarPull, ite_eq_left hb',
        collarShift_of_le_abs hε (symm_snd_of_not_mem_collarCore b hb' hb).le, sub_zero]
      exact c.toPartialEquiv.right_inv hb'
    · rw [collarPull, ite_eq_right hb']
      rfl

theorem baseFlow_collarPull {ε : ℝ} (hε : 0 < ε) (hεw : ε ≤ L.width) (b : F.base.Carrier) :
    L.baseFlow (collarShiftFn c ε b) (collarPull c ε b) = b := by
  rcases collar_cases hε b with ⟨h1, h2⟩ | ⟨hb, hs, h1, h2⟩
  · rw [h1, h2, L.baseFlow_zero]
  · have hsub := abs_sub_collarShift_le ε (c.symm b).2
    rw [h1, h2, L.baseFlow_apply _ _ _ (by linarith) (by rw [sub_add_cancel]; linarith),
      sub_add_cancel]
    exact c.toPartialEquiv.right_inv hb

theorem baseFlow_neg_collarShiftFn {ε : ℝ} (hε : 0 < ε) (hεw : ε ≤ L.width)
    (b : F.base.Carrier) : L.baseFlow (-collarShiftFn c ε b) b = collarPull c ε b := by
  rcases collar_cases hε b with ⟨h1, h2⟩ | ⟨hb, hs, h1, h2⟩
  · rw [h1, h2, neg_zero, L.baseFlow_zero]
  · have hsub := abs_sub_collarShift_le ε (c.symm b).2
    have hb' : c ((c.symm b).1, (c.symm b).2) = b := c.toPartialEquiv.right_inv hb
    have h := L.baseFlow_apply (c.symm b).1 (c.symm b).2 (-collarShift ε (c.symm b).2)
      (by linarith) (by rw [← sub_eq_add_neg]; linarith)
    rw [hb'] at h
    rw [h1, h2, h, ← sub_eq_add_neg]

end LiftedBicollar

theorem collarPull_mem {ε : ℝ} (hε : 0 < ε) (hdom : ∀ θ s, |s| < ε → c (θ, s) ∈ V)
    (b : F.base.Carrier) (hbV : b ∈ V) : collarPull c ε b ∈ V := by
  rcases collar_cases hε b with ⟨-, h⟩ | ⟨-, hs, -, h⟩
  · rw [h]
    exact hbV
  · rw [h]
    exact hdom _ _ (by have := abs_sub_collarShift_le ε (c.symm b).2; linarith)

namespace FibreCoordinate

variable (τ : FibreCoordinate F V) (L : LiftedBicollar F c) {ε : ℝ}

def normalAngle (ε : ℝ) (x : U) : Circle :=
  τ.angle (L.flow (-collarShiftFn c ε (F.projection x)) x)

def normalSymm (hε : 0 < ε) (hdom : ∀ θ s, |s| < ε → c (θ, s) ∈ V) (q : V × Circle) : U :=
  L.flow (collarShiftFn c ε q.1.val)
    (τ.toDiffeo.symm (⟨collarPull c ε q.1.val, collarPull_mem hε hdom q.1.val q.1.2⟩,
      q.2)).val

variable {τ L}

theorem projection_flow_neg (hε : 0 < ε) (hεw : ε ≤ L.width) (x : U) :
    F.projection (L.flow (-collarShiftFn c ε (F.projection x)) x) =
      collarPull c ε (F.projection x) := by
  rw [L.projection_flow, L.baseFlow_neg_collarShiftFn hε hεw]

theorem contMDiffOn_normalAngle (hε : 0 < ε) (hεw : ε ≤ L.width)
    (hdom : ∀ θ s, |s| < ε → c (θ, s) ∈ V) :
    ContMDiffOn C.model (𝓡 1) ∞ (τ.normalAngle L ε)
      (F.projection ⁻¹' (V : Set F.base.Carrier)) := by
  have hg : ContMDiff C.model C.model ∞
      (fun x : U => L.flow (-collarShiftFn c ε (F.projection x)) x) :=
    L.smooth.comp ((contDiff_neg.contMDiff.comp
      ((L.contMDiff_collarShiftFn hε hεw).comp F.smooth)).prodMk contMDiff_id)
  refine τ.contMDiffOn_angle.comp hg.contMDiffOn fun x hx => ?_
  change F.projection _ ∈ V
  rw [projection_flow_neg hε hεw]
  exact collarPull_mem hε hdom _ hx

theorem contMDiff_normalSymm (hε : 0 < ε) (hεw : ε ≤ L.width)
    (hdom : ∀ θ s, |s| < ε → c (θ, s) ∈ V) :
    ContMDiff ((SurfaceModel.model F.base.kind).prod (𝓡 1)) C.model ∞
      (τ.normalSymm L hε hdom) := by
  have hpull : ContMDiff ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      (SurfaceModel.model F.base.kind) ∞
      (fun q : V × Circle => (⟨collarPull c ε q.1.val, collarPull_mem hε hdom q.1.val q.1.2⟩ :
        V)) := by
    apply (ContMDiff.subtypeVal_comp_iff V _).mp
    exact (L.contMDiff_collarPull hε hεw).comp (contMDiff_subtype_val.comp contMDiff_fst)
  have hin := τ.contMDiff_symm_val.comp (hpull.prodMk contMDiff_snd)
  exact L.smooth.comp (((L.contMDiff_collarShiftFn hε hεw).comp
    (contMDiff_subtype_val.comp contMDiff_fst)).prodMk hin)

theorem projection_normalSymm (hε : 0 < ε) (hεw : ε ≤ L.width)
    (hdom : ∀ θ s, |s| < ε → c (θ, s) ∈ V) (q : V × Circle) :
    F.projection (τ.normalSymm L hε hdom q) = q.1.val := by
  rw [normalSymm, L.projection_flow, τ.projection_symm]
  exact L.baseFlow_collarPull hε hεw q.1.val

theorem normalAngle_normalSymm (hε : 0 < ε) (hεw : ε ≤ L.width)
    (hdom : ∀ θ s, |s| < ε → c (θ, s) ∈ V) (q : V × Circle) :
    τ.normalAngle L ε (τ.normalSymm L hε hdom q) = q.2 := by
  rw [normalAngle, projection_normalSymm hε hεw, normalSymm, L.flow_neg_flow, τ.angle_symm]

theorem normalSymm_normalAngle (hε : 0 < ε) (hεw : ε ≤ L.width)
    (hdom : ∀ θ s, |s| < ε → c (θ, s) ∈ V) (x : U) (hx : F.projection x ∈ V) :
    τ.normalSymm L hε hdom (⟨F.projection x, hx⟩, τ.normalAngle L ε x) = x := by
  set y := L.flow (-collarShiftFn c ε (F.projection x)) x
  have hy : F.projection y = collarPull c ε (F.projection x) := projection_flow_neg hε hεw x
  have hyV : F.projection y ∈ V := hy ▸ collarPull_mem hε hdom _ hx
  have hsub : (⟨collarPull c ε (F.projection x), collarPull_mem hε hdom _ hx⟩ : V) =
      ⟨F.projection y, hyV⟩ := Subtype.ext hy.symm
  change L.flow (collarShiftFn c ε (F.projection x))
    (τ.toDiffeo.symm (⟨collarPull c ε (F.projection x), _⟩, τ.angle y)).val = x
  rw [hsub, τ.symm_angle y hyV, L.flow_flow_neg]

def flowNormalized (hε : 0 < ε) (hεw : ε ≤ L.width) (hdom : ∀ θ s, |s| < ε → c (θ, s) ∈ V) :
    FibreCoordinate F V :=
  ofAngle V (τ.normalAngle L ε) (τ.normalSymm L hε hdom) (contMDiffOn_normalAngle hε hεw hdom)
    (contMDiff_normalSymm hε hεw hdom) (projection_normalSymm hε hεw hdom)
    (normalAngle_normalSymm hε hεw hdom) (normalSymm_normalAngle hε hεw hdom)

theorem flowNormalize (τ : FibreCoordinate F V) (L : LiftedBicollar F c) (ε : ℝ) (hε : 0 < ε)
    (hεw : ε ≤ L.width) (hdom : ∀ θ s, |s| < ε → c (θ, s) ∈ V) :
    ∃ τ' : FibreCoordinate F V,
      (∀ x : U, (∀ θ s, |s| < ε → F.projection x ≠ c (θ, s)) → τ'.angle x = τ.angle x) ∧
      (∀ q : V × Circle, (∀ θ s, |s| < ε → q.1.val ≠ c (θ, s)) →
        (τ'.toDiffeo.symm q).val = (τ.toDiffeo.symm q).val) ∧
      ∀ (θ : Circle) (s : ℝ) (v : Circle) (h₁ : c (θ, s) ∈ V) (h₀ : c (θ, 0) ∈ V),
        |s| < ε / 4 → (τ'.toDiffeo.symm (⟨c (θ, s), h₁⟩, v)).val =
          L.flow s (τ'.toDiffeo.symm (⟨c (θ, 0), h₀⟩, v)).val := by
  refine ⟨τ.flowNormalized hε hεw hdom, fun x hx => ?_, fun q hq => ?_, ?_⟩
  · by_cases hxV : F.projection x ∈ V
    · rw [flowNormalized, angle_ofAngle _ _ _ _ _ _ _ _ x hxV, normalAngle,
        collarShiftFn_eq_zero hε _ hx, neg_zero, L.flow_zero]
    · rw [angle, angle, dite_eq_right hxV, dite_eq_right hxV]
  · rw [flowNormalized, symm_ofAngle, normalSymm]
    have hm := collarShiftFn_eq_zero hε _ hq
    have hp : collarPull c ε q.1.val = q.1.val := by
      rcases collar_cases hε q.1.val with ⟨-, h⟩ | ⟨hb, hs, -, -⟩
      · exact h
      · exact absurd (c.toPartialEquiv.right_inv hb).symm
          (hq (c.symm q.1.val).1 (c.symm q.1.val).2 (by linarith))
    have hsub : (⟨collarPull c ε q.1.val, collarPull_mem hε hdom q.1.val q.1.2⟩ : V) = q.1 :=
      Subtype.ext hp
    rw [hm, L.flow_zero, hsub]
  · intro θ s v h₁ h₀ hs
    have hsrc : ∀ r : ℝ, |r| < ε / 4 → (θ, r) ∈ c.source := fun r hr =>
      L.mem_source θ r (by linarith [L.width_lt_reach])
    have hsym : ∀ r : ℝ, |r| < ε / 4 → c.symm (c (θ, r)) = (θ, r) := fun r hr =>
      c.toPartialEquiv.left_inv (hsrc r hr)
    have htg : ∀ r : ℝ, |r| < ε / 4 → c (θ, r) ∈ c.target := fun r hr =>
      c.toPartialEquiv.map_source (hsrc r hr)
    have h0 : |(0 : ℝ)| < ε / 4 := by rw [abs_zero]; linarith
    have hshift : ∀ r : ℝ, |r| < ε / 4 → collarShiftFn c ε (c (θ, r)) = r := fun r hr => by
      rw [collarShiftFn, ite_eq_left (htg r hr), hsym r hr]
      exact collarShift_of_abs_le hε hr.le
    have hpull : ∀ r : ℝ, |r| < ε / 4 → collarPull c ε (c (θ, r)) = c (θ, 0) := fun r hr => by
      rw [collarPull, ite_eq_left (htg r hr), hsym r hr]
      simp only
      rw [collarShift_of_abs_le hε hr.le, sub_self]
    rw [flowNormalized, symm_ofAngle, symm_ofAngle, normalSymm, normalSymm]
    simp only
    have e1 : (⟨collarPull c ε (c (θ, s)), collarPull_mem hε hdom _ h₁⟩ : V) = ⟨c (θ, 0), h₀⟩ :=
      Subtype.ext (hpull s hs)
    have e0 : (⟨collarPull c ε (c (θ, 0)), collarPull_mem hε hdom _ h₀⟩ : V) = ⟨c (θ, 0), h₀⟩ :=
      Subtype.ext (hpull 0 h0)
    rw [e1, e0, hshift s hs, hshift 0 h0, L.flow_zero]

end FibreCoordinate

end FlowNormalize

section Glue

open AnnulusStraightening

theorem simplyConnectedSpace_prod (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y] : SimplyConnectedSpace (X × Y) := by
  rw [simply_connected_iff_paths_homotopic]
  refine ⟨inferInstance, ?_⟩
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  refine ⟨fun p q => ?_⟩
  rw [← Path.Homotopic.prod_projLeft_projRight p, ← Path.Homotopic.prod_projLeft_projRight q]
  congr 1 <;> exact Subsingleton.elim _ _

variable {F : CircleFibration C U} {V V₁ V₂ : TopologicalSpace.Opens F.base.Carrier}

theorem mfderiv_fibrewise_fst {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {h : M × Circle → Circle} {p : M × Circle}
    (hh : MDifferentiableAt (I.prod (𝓡 1)) (𝓡 1) h p) (v : E × EuclideanSpace ℝ (Fin 1)) :
    (mfderiv (I.prod (𝓡 1)) (I.prod (𝓡 1)) (fun q => (q.1, h q)) p v).1 = v.1 := by
  rw [mfderiv_prodMk mdifferentiableAt_fst hh, mfderiv_fst]
  rfl

theorem mfderiv_fibrewise_vert {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {h : M × Circle → Circle} {p : M × Circle}
    (hh : MDifferentiableAt (I.prod (𝓡 1)) (𝓡 1) h p) (w : EuclideanSpace ℝ (Fin 1)) :
    mfderiv (I.prod (𝓡 1)) (I.prod (𝓡 1)) (fun q => (q.1, h q)) p ((0 : E), w) =
      ((0 : E), mfderiv (𝓡 1) (𝓡 1) (fun z => h (p.1, z)) p.2 w) := by
  rw [mfderiv_prodMk mdifferentiableAt_fst hh, mfderiv_fst]
  refine Prod.ext rfl ?_
  have hsum := mfderiv_prod_eq_add_apply (I := I) (I' := 𝓡 1) (I'' := 𝓡 1) (f := h) (p := p)
    (v := ((0 : E), w)) hh
  refine hsum.trans ?_
  have h0 : mfderiv I (𝓡 1) (fun z => h (z, p.2)) p.1
      (((0 : E), w) : E × EuclideanSpace ℝ (Fin 1)).1 = 0 := map_zero _
  rw [h0, zero_add]

namespace FibreCoordinate

theorem orientation_map_ambient
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
    (τ : FibreCoordinate F V) (hτ : τ.IsPositive (o.restrictOpen V)) (x : U)
    (hx : F.projection x ∈ V)
    (L : TangentSpace C.model x ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)))
    (hL : ∀ v, L v = mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      (fun y : U => (F.projection y, τ.angle y)) x v) :
    Orientation.map (Fin 3) L ((C.orientation.restrictOpen U).orientation x) =
      (CircleFibration.baseProductOrientation F o).orientation (F.projection x, τ.angle x) := by
  let x' : TopologicalSpace.Opens.comap F.projection V := ⟨x, hx⟩
  have hLe : L = (τ.toDiffeo.mfderivToContinuousLinearEquiv (by simp) x').toLinearEquiv :=
    LinearEquiv.ext fun v => by
      rw [hL]
      change _ = mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1)) τ.toDiffeo x' v
      rw [τ.mfderiv_toDiffeo_apply x' v]
  have h := hτ x'
  rw [CircleFibration.productOrientation_restrictOpen] at h
  have hpt : (((τ.toDiffeo x').1.val, (τ.toDiffeo x').2) : F.base.Carrier × Circle) =
      (F.projection x, τ.angle x) :=
    Prod.ext (τ.fst_eq x') (τ.angle_of_mem x hx).symm
  rw [hpt] at h
  rw [hLe]
  exact h

theorem isPositive_of_ambient
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
    (τ : FibreCoordinate F V)
    (h : ∀ (x : U) (_ : F.projection x ∈ V)
      (L : TangentSpace C.model x ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))),
      (∀ v, L v = mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1))
        (fun y : U => (F.projection y, τ.angle y)) x v) →
      Orientation.map (Fin 3) L ((C.orientation.restrictOpen U).orientation x) =
        (CircleFibration.baseProductOrientation F o).orientation (F.projection x, τ.angle x)) :
    τ.IsPositive (o.restrictOpen V) := by
  intro x'
  have hx := h x'.val x'.2 (τ.toDiffeo.mfderivToContinuousLinearEquiv (by simp) x').toLinearEquiv
    (fun v => τ.mfderiv_toDiffeo_apply x' v)
  change Orientation.map (Fin 3) ((τ.toDiffeo.mfderivToContinuousLinearEquiv (by simp)
    x').toLinearEquiv) ((C.orientation.restrictOpen U).orientation x'.val) = _
  have hpt : (((τ.toDiffeo x').1.val, (τ.toDiffeo x').2) : F.base.Carrier × Circle) =
      (F.projection x'.val, τ.angle x'.val) :=
    Prod.ext (τ.fst_eq x') (τ.angle_of_mem x'.val x'.2).symm
  rw [CircleFibration.productOrientation_restrictOpen, hpt]
  exact hx

theorem orientation_map_fibrewise_lift
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
    (τ : FibreCoordinate F V) (hτ : τ.IsPositive (o.restrictOpen V)) {x : U}
    (hx : F.projection x ∈ V) {θ : U → Circle} {h : F.base.Carrier × Circle → Circle}
    (hθ : ∀ᶠ y in 𝓝 x, θ y = h (F.projection y, τ.angle y))
    (hh : MDifferentiableAt ((SurfaceModel.model F.base.kind).prod (𝓡 1)) (𝓡 1) h
      (F.projection x, τ.angle x))
    {Gs : ℝ → ℝ} {t₀ G' : ℝ} (hz : τ.angle x = cexp t₀) (hG : HasDerivAt Gs G' t₀)
    (hlift : (fun t => h (F.projection x, cexp t)) =ᶠ[𝓝 t₀] fun t => cexp (Gs t))
    (L : TangentSpace C.model x ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)))
    (hL : ∀ v, L v = mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      (fun y : U => (F.projection y, θ y)) x v) :
    G' ≠ 0 ∧
      (0 < G' → Orientation.map (Fin 3) L ((C.orientation.restrictOpen U).orientation x) =
        (CircleFibration.baseProductOrientation F o).orientation
          (F.projection x, cexp (Gs t₀))) ∧
      (G' < 0 → Orientation.map (Fin 3) L ((C.orientation.restrictOpen U).orientation x) =
        -(CircleFibration.baseProductOrientation F o).orientation
          (F.projection x, cexp (Gs t₀))) := by
  set b := F.projection x
  have hA : MDifferentiableAt C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      (fun y : U => (F.projection y, τ.angle y)) x :=
    (F.smooth.mdifferentiableAt (by simp)).prodMk
      ((τ.contMDiffOn_angle.contMDiffAt ((isOpen_preimage V).mem_nhds hx)).mdifferentiableAt
        (by simp))
  let La : TangentSpace C.model x ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) :=
    (τ.toDiffeo.mfderivToContinuousLinearEquiv (by simp) ⟨x, hx⟩).toLinearEquiv
  have hLa : ∀ v, La v = mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      (fun y : U => (F.projection y, τ.angle y)) x v :=
    fun v => τ.mfderiv_toDiffeo_apply ⟨x, hx⟩ v
  have hLaO := τ.orientation_map_ambient o hτ x hx La hLa
  rw [hz] at hLaO
  let M : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) := La.symm.trans L
  let Ψ : F.base.Carrier × Circle → F.base.Carrier × Circle := fun q => (q.1, h q)
  have hΨd : MDifferentiableAt ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      ((SurfaceModel.model F.base.kind).prod (𝓡 1)) Ψ (b, τ.angle x) :=
    mdifferentiableAt_fst.prodMk hh
  have hΨ : ∀ v, M v = mfderiv ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      ((SurfaceModel.model F.base.kind).prod (𝓡 1)) Ψ (b, τ.angle x) v := by
    intro v
    change L (La.symm v) = _
    have hev : (fun y : U => (F.projection y, θ y)) =ᶠ[𝓝 x]
        Ψ ∘ fun y : U => (F.projection y, τ.angle y) :=
      hθ.mono fun y hy => Prod.ext rfl hy
    rw [hL, hev.mfderiv_eq]
    change mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      (Ψ ∘ fun y : U => (F.projection y, τ.angle y)) x (La.symm v) = _
    rw [mfderiv_comp_apply x hΨd hA, ← hLa, LinearEquiv.apply_symm_apply]
  have h1 : ∀ v, (M v).1 = v.1 := fun v => by
    rw [hΨ]
    exact mfderiv_fibrewise_fst hh v
  have h2 : ∀ w : EuclideanSpace ℝ (Fin 1), M (0, w) =
      (0, mfderiv (𝓡 1) (𝓡 1) (fun z => h (b, z)) (τ.angle x) w) := fun w => by
    rw [hΨ]
    exact mfderiv_fibrewise_vert hh w
  have hg : MDifferentiableAt (𝓡 1) (𝓡 1) (fun z => h (b, z)) (cexp t₀) := by
    rw [← hz]
    exact hh.comp (τ.angle x) (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  let D : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1) :=
    { toFun := fun w => mfderiv (𝓡 1) (𝓡 1) (fun z => h (b, z)) (τ.angle x) w
      map_add' := fun w w' => map_add _ w w'
      map_smul' := fun c w => map_smul _ c w }
  have hinj : Function.Injective D := by
    intro w w' hww
    have hM : M (0, w) = M (0, w') :=
      (h2 w).trans ((congrArg (Prod.mk (0 : EuclideanSpace ℝ (Fin 2))) hww).trans (h2 w').symm)
    exact congrArg Prod.snd (M.injective hM)
  let A : EuclideanSpace ℝ (Fin 1) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1) :=
    LinearEquiv.ofInjectiveEndo D hinj
  have hAdef : ∀ w, A w = mfderiv (𝓡 1) (𝓡 1) (fun z => h (b, z)) (cexp t₀) w := fun w => by
    rw [← hz]
    rfl
  have h2' : ∀ w : EuclideanSpace ℝ (Fin 1), M (0, w) = (0, A w) := h2
  have hne : G' ≠ 0 := by
    intro h0
    have hc := cexp_lift_mfderiv hg hG hlift 1
    rw [h0, zero_mul, map_zero] at hc
    have h3 : cexpDeriv t₀ 1 = 0 := A.injective
      (((hAdef _).trans hc).trans (map_zero A).symm)
    exact one_ne_zero ((cexpDeriv t₀).injective (h3.trans (map_zero _).symm))
  have hLM : L = La.trans M := LinearEquiv.ext fun v => by
    change L v = L (La.symm (La v))
    rw [LinearEquiv.symm_apply_apply]
  refine ⟨hne, fun hpos => ?_, fun hneg => ?_⟩
  · have hAo := orientation_map_of_cexp_lift circleOrientation hg hG hpos hlift A hAdef
    have hM := orientation_map_fibrewise o circleOrientation circleOrientation b (cexp t₀)
      (cexp (Gs t₀)) A hAo M h1 h2'
    rw [hLM, orientation_map_trans_fin, hLaO]
    exact hM
  · have hAo := orientation_map_of_cexp_lift_neg circleOrientation hg hG hneg hlift A hAdef
    have hM := orientation_map_fibrewise o circleOrientation circleOrientation.opposite b
      (cexp t₀) (cexp (Gs t₀)) A hAo M h1 h2'
    rw [← productOrientation_opposite_right, ManifoldOrientation.opposite_orientation] at hM
    rw [hLM, orientation_map_trans_fin, hLaO]
    exact hM

end FibreCoordinate

namespace FibreCoordinate

theorem orientation_map_of_angle_eventuallyEq {W : TopologicalSpace.Opens F.base.Carrier}
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
    (τ' : FibreCoordinate F W) (hτ' : τ'.IsPositive (o.restrictOpen W)) {x : U}
    (hx : F.projection x ∈ W) {θ : U → Circle} (hθ : θ =ᶠ[𝓝 x] τ'.angle)
    (L : TangentSpace C.model x ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)))
    (hL : ∀ v, L v = mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      (fun y : U => (F.projection y, θ y)) x v) :
    Orientation.map (Fin 3) L ((C.orientation.restrictOpen U).orientation x) =
      (CircleFibration.baseProductOrientation F o).orientation (F.projection x, θ x) := by
  have hev : (fun y : U => (F.projection y, θ y)) =ᶠ[𝓝 x]
      fun y : U => (F.projection y, τ'.angle y) :=
    hθ.mono fun y hy => congrArg (Prod.mk (F.projection y)) hy
  have hL' : ∀ v, L v = mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      (fun y : U => (F.projection y, τ'.angle y)) x v := fun v => by
    rw [hL, hev.mfderiv_eq]
    rfl
  rw [τ'.orientation_map_ambient o hτ' x hx L hL', hθ.eq_of_nhds]

open scoped Classical in
def symmFn (τ : FibreCoordinate F V) (b : F.base.Carrier) (z : Circle) : U :=
  if h : b ∈ V then (τ.toDiffeo.symm (⟨b, h⟩, z)).val else (F.surjective b).choose

theorem symmFn_of_mem (τ : FibreCoordinate F V) {b : F.base.Carrier} (h : b ∈ V) (z : Circle) :
    τ.symmFn b z = (τ.toDiffeo.symm (⟨b, h⟩, z)).val :=
  dite_eq_left h

theorem projection_symmFn (τ : FibreCoordinate F V) (b : F.base.Carrier) (z : Circle) :
    F.projection (τ.symmFn b z) = b := by
  by_cases h : b ∈ V
  · rw [τ.symmFn_of_mem h]
    exact τ.projection_symm _
  · rw [symmFn, dite_eq_right h]
    exact (F.surjective b).choose_spec

theorem angle_symmFn (τ : FibreCoordinate F V) {b : F.base.Carrier} (h : b ∈ V) (z : Circle) :
    τ.angle (τ.symmFn b z) = z := by
  rw [τ.symmFn_of_mem h]
  exact τ.angle_symm _

theorem symmFn_angle (τ : FibreCoordinate F V) (x : U) (hx : F.projection x ∈ V) :
    τ.symmFn (F.projection x) (τ.angle x) = x := by
  rw [τ.symmFn_of_mem hx]
  exact τ.symm_angle x hx

theorem contMDiffOn_symmFn (τ : FibreCoordinate F V) :
    ContMDiffOn ((SurfaceModel.model F.base.kind).prod (𝓡 1)) C.model ∞
      (fun p : F.base.Carrier × Circle => τ.symmFn p.1 p.2) ((V : Set F.base.Carrier) ×ˢ univ) := by
  let W : TopologicalSpace.Opens (F.base.Carrier × Circle) :=
    ⟨(V : Set F.base.Carrier) ×ˢ univ, V.isOpen.prod isOpen_univ⟩
  intro p hp
  have he : ContMDiff ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      ((SurfaceModel.model F.base.kind).prod (𝓡 1)) ∞
      (fun w : W => ((⟨w.val.1, w.2.1⟩ : V), w.val.2)) := by
    refine ContMDiff.prodMk ?_ (contMDiff_snd.comp contMDiff_subtype_val)
    apply (ContMDiff.subtypeVal_comp_iff V _).mp
    exact contMDiff_fst.comp contMDiff_subtype_val
  have hW : ContMDiff ((SurfaceModel.model F.base.kind).prod (𝓡 1)) C.model ∞
      (fun w : W => τ.symmFn w.val.1 w.val.2) :=
    (τ.contMDiff_symm_val.comp he).congr fun w => τ.symmFn_of_mem w.2.1 w.val.2
  exact ((contMDiffAt_subtype_iff (U := W)
    (f := fun p : F.base.Carrier × Circle => τ.symmFn p.1 p.2) (x := ⟨p, hp⟩)).mp
    (hW ⟨p, hp⟩)).contMDiffWithinAt

def transitionAngle (τ₁ : FibreCoordinate F V₁) (τ₂ : FibreCoordinate F V₂)
    (b : F.base.Carrier) (z : Circle) : Circle :=
  τ₂.angle (τ₁.symmFn b z)

variable (τ₁ : FibreCoordinate F V₁) (τ₂ : FibreCoordinate F V₂)

theorem contMDiffOn_transitionAngle :
    ContMDiffOn ((SurfaceModel.model F.base.kind).prod (𝓡 1)) (𝓡 1) ∞
      (fun p : F.base.Carrier × Circle => transitionAngle τ₁ τ₂ p.1 p.2)
      (((V₁ ⊓ V₂ : TopologicalSpace.Opens F.base.Carrier) : Set F.base.Carrier) ×ˢ univ) := by
  refine τ₂.contMDiffOn_angle.comp (τ₁.contMDiffOn_symmFn.mono
    (prod_mono (fun b hb => hb.1) subset_rfl)) fun p hp => ?_
  change F.projection (τ₁.symmFn p.1 p.2) ∈ V₂
  rw [projection_symmFn]
  exact hp.1.2

theorem transitionAngle_injective {b : F.base.Carrier} (hb : b ∈ V₁ ⊓ V₂) :
    Function.Injective (transitionAngle τ₁ τ₂ b) := by
  intro z z' h
  have hm : ∀ w, F.projection (τ₁.symmFn b w) ∈ V₂ := fun w => by
    rw [projection_symmFn]
    exact hb.2
  have h1 : τ₁.symmFn b z = τ₁.symmFn b z' := by
    rw [← τ₂.symmFn_angle (τ₁.symmFn b z) (hm z), ← τ₂.symmFn_angle (τ₁.symmFn b z') (hm z'),
      projection_symmFn, projection_symmFn]
    exact congrArg (τ₂.symmFn b) h
  rw [← τ₁.angle_symmFn hb.1 z, ← τ₁.angle_symmFn hb.1 z', h1]

theorem exists_transition_lift {O' : TopologicalSpace.Opens F.base.Carrier}
    (hO' : O' ≤ V₁ ⊓ V₂) (hsc : IsSimplyConnected (O' : Set F.base.Carrier)) :
    ∃ K : O' × ℝ → ℝ, ContMDiff ((SurfaceModel.model F.base.kind).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ K ∧
      ∀ q, cexp (K q) = transitionAngle τ₁ τ₂ q.1.val (cexp q.2) := by
  have : SimplyConnectedSpace O' := hsc.simplyConnectedSpace
  have : SimplyConnectedSpace (O' × ℝ) := simplyConnectedSpace_prod O' ℝ
  have : LocallyPathConnectedSpace (SurfaceModel.Space F.base.kind) :=
    locallyPathConnectedSpace_surfaceModel F.base.kind
  have : LocallyPathConnectedSpace O' :=
    ChartedSpace.locallyPathConnectedSpace (SurfaceModel.Space F.base.kind) O'
  have hf : ContMDiff ((SurfaceModel.model F.base.kind).prod 𝓘(ℝ, ℝ)) (𝓡 1) ∞
      (fun q : O' × ℝ => transitionAngle τ₁ τ₂ q.1.val (cexp q.2)) := by
    have hin : ContMDiff ((SurfaceModel.model F.base.kind).prod 𝓘(ℝ, ℝ))
        ((SurfaceModel.model F.base.kind).prod (𝓡 1)) ∞
        (fun q : O' × ℝ => (q.1.val, cexp q.2)) :=
      (contMDiff_subtype_val.comp contMDiff_fst).prodMk (contMDiff_cexp.comp contMDiff_snd)
    exact (contMDiffOn_transitionAngle τ₁ τ₂).comp_contMDiff hin fun q =>
      ⟨hO' q.1.2, mem_univ _⟩
  obtain ⟨K, hKc, hK⟩ := exists_continuous_cexp_lift hf.continuous
  exact ⟨K, isLocalDiffeomorph_cexp.contMDiff_of_continuous_of_comp hKc
    (hf.congr fun q => hK q) le_rfl, hK⟩


open scoped Classical in
def liftOn (O' : TopologicalSpace.Opens F.base.Carrier) (p : F.base.Carrier × ℝ) : ℝ :=
  if h : O' ≤ V₁ ⊓ V₂ ∧ IsSimplyConnected (O' : Set F.base.Carrier) ∧ p.1 ∈ O' then
    (exists_transition_lift τ₁ τ₂ h.1 h.2.1).choose (⟨p.1, h.2.2⟩, p.2)
  else 0

theorem liftOn_eq {O' : TopologicalSpace.Opens F.base.Carrier} (hO' : O' ≤ V₁ ⊓ V₂)
    (hsc : IsSimplyConnected (O' : Set F.base.Carrier)) {p : F.base.Carrier × ℝ}
    (hp : p.1 ∈ O') :
    liftOn τ₁ τ₂ O' p = (exists_transition_lift τ₁ τ₂ hO' hsc).choose (⟨p.1, hp⟩, p.2) :=
  dite_eq_left ⟨hO', hsc, hp⟩

theorem liftOn_of_not_mem {O' : TopologicalSpace.Opens F.base.Carrier}
    {p : F.base.Carrier × ℝ} (hp : p.1 ∉ O') : liftOn τ₁ τ₂ O' p = 0 :=
  dite_eq_right fun h => hp h.2.2

theorem cexp_liftOn {O' : TopologicalSpace.Opens F.base.Carrier} (hO' : O' ≤ V₁ ⊓ V₂)
    (hsc : IsSimplyConnected (O' : Set F.base.Carrier)) {p : F.base.Carrier × ℝ}
    (hp : p.1 ∈ O') : cexp (liftOn τ₁ τ₂ O' p) = transitionAngle τ₁ τ₂ p.1 (cexp p.2) := by
  rw [liftOn_eq τ₁ τ₂ hO' hsc hp]
  exact (exists_transition_lift τ₁ τ₂ hO' hsc).choose_spec.2 _

theorem contMDiffOn_liftOn {O' : TopologicalSpace.Opens F.base.Carrier} (hO' : O' ≤ V₁ ⊓ V₂)
    (hsc : IsSimplyConnected (O' : Set F.base.Carrier)) :
    ContMDiffOn ((SurfaceModel.model F.base.kind).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (liftOn τ₁ τ₂ O')
      ((O' : Set F.base.Carrier) ×ˢ univ) := by
  let W : TopologicalSpace.Opens (F.base.Carrier × ℝ) :=
    ⟨(O' : Set F.base.Carrier) ×ˢ univ, O'.isOpen.prod isOpen_univ⟩
  intro p hp
  have he : ContMDiff ((SurfaceModel.model F.base.kind).prod 𝓘(ℝ, ℝ))
      ((SurfaceModel.model F.base.kind).prod 𝓘(ℝ, ℝ)) ∞
      (fun w : W => ((⟨w.val.1, w.2.1⟩ : O'), w.val.2)) := by
    refine ContMDiff.prodMk ?_ (contMDiff_snd.comp contMDiff_subtype_val)
    apply (ContMDiff.subtypeVal_comp_iff O' _).mp
    exact contMDiff_fst.comp contMDiff_subtype_val
  have hW : ContMDiff ((SurfaceModel.model F.base.kind).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun w : W => liftOn τ₁ τ₂ O' w.val) :=
    ((exists_transition_lift τ₁ τ₂ hO' hsc).choose_spec.1.comp he).congr fun w =>
      liftOn_eq τ₁ τ₂ hO' hsc w.2.1
  exact ((contMDiffAt_subtype_iff (U := W) (f := liftOn τ₁ τ₂ O') (x := ⟨p, hp⟩)).mp
    (hW ⟨p, hp⟩)).contMDiffWithinAt

def transitionLift (O : Finset (TopologicalSpace.Opens F.base.Carrier))
    (p : F.base.Carrier × ℝ) : ℝ :=
  ∑ O' ∈ O, liftOn τ₁ τ₂ O' p

theorem transitionLift_eq {O : Finset (TopologicalSpace.Opens F.base.Carrier)}
    (hO : (O : Set (TopologicalSpace.Opens F.base.Carrier)).PairwiseDisjoint id)
    {O' : TopologicalSpace.Opens F.base.Carrier} (hO' : O' ∈ O) {p : F.base.Carrier × ℝ}
    (hp : p.1 ∈ O') : transitionLift τ₁ τ₂ O p = liftOn τ₁ τ₂ O' p := by
  unfold transitionLift
  refine Finset.sum_eq_single O' (fun O'' hO'' hne => liftOn_of_not_mem τ₁ τ₂ fun h => ?_)
    fun h => absurd hO' h
  have hd : Disjoint O'' O' := hO hO'' hO' hne
  have hm : p.1 ∈ O'' ⊓ O' := ⟨h, hp⟩
  rw [hd.eq_bot] at hm
  exact hm

variable {τ₁ τ₂}


variable {O : Finset (TopologicalSpace.Opens F.base.Carrier)}

theorem exists_mem_cover (hcov : V₁ ⊓ V₂ = ⨆ O' ∈ O, O') {b : F.base.Carrier}
    (hb : b ∈ V₁ ⊓ V₂) : ∃ O' ∈ O, b ∈ O' := by
  rw [hcov] at hb
  obtain ⟨O', hb'⟩ := TopologicalSpace.Opens.mem_iSup.mp hb
  obtain ⟨hO', hbO'⟩ := TopologicalSpace.Opens.mem_iSup.mp hb'
  exact ⟨O', hO', hbO'⟩

theorem le_of_mem_cover (hcov : V₁ ⊓ V₂ = ⨆ O' ∈ O, O')
    {O' : TopologicalSpace.Opens F.base.Carrier} (hO' : O' ∈ O) : O' ≤ V₁ ⊓ V₂ := by
  rw [hcov]
  exact le_iSup₂ (f := fun O'' (_ : O'' ∈ O) => O'') O' hO'

theorem cexp_transitionLift (hcov : V₁ ⊓ V₂ = ⨆ O' ∈ O, O')
    (hdis : (O : Set (TopologicalSpace.Opens F.base.Carrier)).PairwiseDisjoint id)
    (hsc : ∀ O' ∈ O, IsSimplyConnected (O' : Set F.base.Carrier)) {p : F.base.Carrier × ℝ}
    (hp : p.1 ∈ V₁ ⊓ V₂) :
    cexp (transitionLift τ₁ τ₂ O p) = transitionAngle τ₁ τ₂ p.1 (cexp p.2) := by
  obtain ⟨O', hO', hpO'⟩ := exists_mem_cover hcov hp
  rw [transitionLift_eq τ₁ τ₂ hdis hO' hpO']
  exact cexp_liftOn τ₁ τ₂ (le_of_mem_cover hcov hO') (hsc O' hO') hpO'

theorem contMDiffOn_transitionLift (hcov : V₁ ⊓ V₂ = ⨆ O' ∈ O, O')
    (hdis : (O : Set (TopologicalSpace.Opens F.base.Carrier)).PairwiseDisjoint id)
    (hsc : ∀ O' ∈ O, IsSimplyConnected (O' : Set F.base.Carrier)) :
    ContMDiffOn ((SurfaceModel.model F.base.kind).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (transitionLift τ₁ τ₂ O)
      (((V₁ ⊓ V₂ : TopologicalSpace.Opens F.base.Carrier) : Set F.base.Carrier) ×ˢ univ) := by
  intro p hp
  obtain ⟨O', hO', hpO'⟩ := exists_mem_cover hcov hp.1
  have hopen : ((O' : Set F.base.Carrier) ×ˢ (univ : Set ℝ)) ∈ 𝓝 p :=
    (O'.isOpen.prod isOpen_univ).mem_nhds ⟨hpO', mem_univ _⟩
  have h1 := (contMDiffOn_liftOn τ₁ τ₂ (le_of_mem_cover hcov hO') (hsc O' hO')).contMDiffAt hopen
  refine (h1.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hopen] with q hq
  exact transitionLift_eq τ₁ τ₂ hdis hO' hq.1

theorem hasDerivAt_slice {G : F.base.Carrier × ℝ → ℝ} {W : Set F.base.Carrier} (hW : IsOpen W)
    (hG : ContMDiffOn ((SurfaceModel.model F.base.kind).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ G (W ×ˢ univ))
    {b : F.base.Carrier} (hb : b ∈ W) (t : ℝ) :
    HasDerivAt (fun s => G (b, s)) (deriv (fun s => G (b, s)) t) t := by
  have h1 : ContMDiffAt ((SurfaceModel.model F.base.kind).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ G (b, t) :=
    hG.contMDiffAt ((hW.prod isOpen_univ).mem_nhds ⟨hb, mem_univ _⟩)
  have h2 : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => G (b, s)) t :=
    h1.comp t (contMDiffAt_const.prodMk contMDiffAt_id)
  exact ((contMDiffAt_iff_contDiffAt.mp h2).differentiableAt (by simp)).hasDerivAt

theorem continuous_slice {G : F.base.Carrier × ℝ → ℝ} {W : Set F.base.Carrier} (hW : IsOpen W)
    (hG : ContMDiffOn ((SurfaceModel.model F.base.kind).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ G (W ×ˢ univ))
    {b : F.base.Carrier} (hb : b ∈ W) : Continuous fun s => G (b, s) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_slice hW hG hb t).continuousAt

theorem deriv_transitionLift_pos
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
    (h₁ : τ₁.IsPositive (o.restrictOpen V₁)) (h₂ : τ₂.IsPositive (o.restrictOpen V₂))
    (hcov : V₁ ⊓ V₂ = ⨆ O' ∈ O, O')
    (hdis : (O : Set (TopologicalSpace.Opens F.base.Carrier)).PairwiseDisjoint id)
    (hsc : ∀ O' ∈ O, IsSimplyConnected (O' : Set F.base.Carrier)) {b : F.base.Carrier}
    (hb : b ∈ V₁ ⊓ V₂) (t : ℝ) : 0 < deriv (fun s => transitionLift τ₁ τ₂ O (b, s)) t := by
  set x := τ₁.symmFn b (cexp t)
  have hπx : F.projection x = b := τ₁.projection_symmFn b (cexp t)
  have hx₁ : F.projection x ∈ V₁ := hπx ▸ hb.1
  have hx₂ : F.projection x ∈ V₂ := hπx ▸ hb.2
  have hV₁₂ : IsOpen (((V₁ ⊓ V₂ : TopologicalSpace.Opens F.base.Carrier) :
      Set F.base.Carrier)) := (V₁ ⊓ V₂).isOpen
  have hKsm := contMDiffOn_transitionLift (τ₁ := τ₁) (τ₂ := τ₂) hcov hdis hsc
  have hθ : ∀ᶠ y in 𝓝 x, τ₂.angle y =
      (fun q : F.base.Carrier × Circle => transitionAngle τ₁ τ₂ q.1 q.2)
        (F.projection y, τ₁.angle y) := by
    filter_upwards [(isOpen_preimage V₁).mem_nhds hx₁] with y hy
    change τ₂.angle y = τ₂.angle (τ₁.symmFn (F.projection y) (τ₁.angle y))
    rw [τ₁.symmFn_angle y hy]
  have hh : MDifferentiableAt ((SurfaceModel.model F.base.kind).prod (𝓡 1)) (𝓡 1)
      (fun q : F.base.Carrier × Circle => transitionAngle τ₁ τ₂ q.1 q.2)
      (F.projection x, τ₁.angle x) := by
    refine ((contMDiffOn_transitionAngle τ₁ τ₂).contMDiffAt
      ((hV₁₂.prod isOpen_univ).mem_nhds ⟨?_, mem_univ _⟩)).mdifferentiableAt (by simp)
    rw [hπx]
    exact hb
  have hz : τ₁.angle x = cexp t := τ₁.angle_symmFn hb.1 (cexp t)
  have hG := hasDerivAt_slice hV₁₂ hKsm hb t
  have hlift : (fun s => (fun q : F.base.Carrier × Circle => transitionAngle τ₁ τ₂ q.1 q.2)
      (F.projection x, cexp s)) =ᶠ[𝓝 t]
        fun s => cexp (transitionLift τ₁ τ₂ O (b, s)) :=
    Filter.Eventually.of_forall fun s => by
      change transitionAngle τ₁ τ₂ (F.projection x) (cexp s) =
        cexp (transitionLift τ₁ τ₂ O (b, s))
      rw [hπx, cexp_transitionLift hcov hdis hsc (p := (b, s)) hb]
  let L₂ : TangentSpace C.model x ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) :=
    (τ₂.toDiffeo.mfderivToContinuousLinearEquiv (by simp) ⟨x, hx₂⟩).toLinearEquiv
  have hL₂ : ∀ v, L₂ v = mfderiv C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      (fun y : U => (F.projection y, τ₂.angle y)) x v :=
    fun v => τ₂.mfderiv_toDiffeo_apply ⟨x, hx₂⟩ v
  obtain ⟨hne, -, hneg⟩ := orientation_map_fibrewise_lift o τ₁ h₁ hx₁ hθ hh hz hG hlift L₂ hL₂
  have hpos₂ := τ₂.orientation_map_ambient o h₂ x hx₂ L₂ hL₂
  have hpt : τ₂.angle x = cexp (transitionLift τ₁ τ₂ O (b, t)) := by
    rw [cexp_transitionLift hcov hdis hsc (p := (b, t)) hb, ← hz]
    change τ₂.angle x = τ₂.angle (τ₁.symmFn b (τ₁.angle x))
    rw [hz]
  rw [hpt] at hpos₂
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exfalso
    have h3 := hneg hlt
    rw [hpos₂, hπx] at h3
    exact Module.Ray.ne_neg_self _ h3
  · exact hgt

theorem transitionLift_add_one
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
    (h₁ : τ₁.IsPositive (o.restrictOpen V₁)) (h₂ : τ₂.IsPositive (o.restrictOpen V₂))
    (hcov : V₁ ⊓ V₂ = ⨆ O' ∈ O, O')
    (hdis : (O : Set (TopologicalSpace.Opens F.base.Carrier)).PairwiseDisjoint id)
    (hsc : ∀ O' ∈ O, IsSimplyConnected (O' : Set F.base.Carrier)) {b : F.base.Carrier}
    (hb : b ∈ V₁ ⊓ V₂) (t : ℝ) :
    transitionLift τ₁ τ₂ O (b, t + 1) = transitionLift τ₁ τ₂ O (b, t) + 1 := by
  set K := fun s => transitionLift τ₁ τ₂ O (b, s)
  have hV₁₂ : IsOpen (((V₁ ⊓ V₂ : TopologicalSpace.Opens F.base.Carrier) :
      Set F.base.Carrier)) := (V₁ ⊓ V₂).isOpen
  have hKsm := contMDiffOn_transitionLift (τ₁ := τ₁) (τ₂ := τ₂) hcov hdis hsc
  have hc : Continuous K := continuous_slice hV₁₂ hKsm hb
  have hcexp : ∀ s, cexp (K s) = transitionAngle τ₁ τ₂ b (cexp s) := fun s =>
    cexp_transitionLift hcov hdis hsc (p := (b, s)) hb
  have hper : ∀ s, cexp (K (s + 1)) = cexp (K s) := fun s => by
    rw [hcexp, hcexp]
    congr 1
    exact_mod_cast cexp_add_int s 1
  obtain ⟨n, hn⟩ := exists_int_of_cexp_eq (F := K) (F' := fun s => K (s + 1)) hc
    (hc.comp (continuous_id.add continuous_const)) (fun s => hper s) 0
  have hmono : StrictMono K :=
    strictMono_of_deriv_pos fun s => deriv_transitionLift_pos o h₁ h₂ hcov hdis hsc hb s
  have hn0 : (0 : ℝ) < n := by
    have h01 := hmono (show (0 : ℝ) < 0 + 1 by norm_num)
    have := hn 0
    linarith
  have hle : K 0 + 1 ≤ K 1 := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show (1 : ℤ) ≤ n by exact_mod_cast hn0)
    have := hn 0
    rw [zero_add] at this
    linarith
  obtain ⟨c, hc01, hcK⟩ := intermediate_value_Icc (zero_le_one' ℝ) hc.continuousOn
    ⟨by linarith, hle⟩
  have hcc : cexp c = cexp 0 := by
    apply transitionAngle_injective τ₁ τ₂ hb
    rw [← hcexp, ← hcexp, hcK]
    exact_mod_cast cexp_add_int (K 0) 1
  obtain ⟨m, hm⟩ := cexp_eq_cexp_iff.mp hcc
  have hc1 : c = 1 := by
    rw [zero_add] at hm
    have hm0 : (0 : ℝ) ≤ m := hm ▸ hc01.1
    have hm1 : (m : ℝ) ≤ 1 := hm ▸ hc01.2
    have hm0' : 0 ≤ m := by exact_mod_cast hm0
    have hm1' : m ≤ 1 := by exact_mod_cast hm1
    rcases (show m = 0 ∨ m = 1 by omega) with h | h
    · exfalso
      rw [h, Int.cast_zero] at hm
      rw [hm] at hcK
      linarith
    · rw [hm, h, Int.cast_one]
  rw [hc1] at hcK
  have hn1 : (n : ℝ) = 1 := by
    have := hn 0
    rw [zero_add] at this
    linarith
  have ht := hn t
  calc transitionLift τ₁ τ₂ O (b, t + 1) = K (t + 1) := rfl
    _ = K t + n := ht
    _ = transitionLift τ₁ τ₂ O (b, t) + 1 := by rw [hn1]

theorem add_int_of_add_one {f : ℝ → ℝ} (h : ∀ t, f (t + 1) = f t + 1) (t : ℝ) (n : ℤ) :
    f (t + n) = f t + n := by
  have hP : Function.Periodic (fun y => f y - y) 1 := fun y => by
    simp only
    rw [h]
    ring
  have h1 := hP.int_mul n t
  simp only [mul_one] at h1
  linarith

theorem contMDiffOn_cexp_rep {Φ : F.base.Carrier × ℝ → ℝ} {W : Set F.base.Carrier}
    (hW : IsOpen W)
    (hΦ : ContMDiffOn ((SurfaceModel.model F.base.kind).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ Φ (W ×ˢ univ))
    (hper : ∀ b ∈ W, ∀ (t : ℝ) (n : ℤ), Φ (b, t + n) = Φ (b, t) + n) :
    ContMDiffOn ((SurfaceModel.model F.base.kind).prod (𝓡 1)) (𝓡 1) ∞
      (fun p : F.base.Carrier × Circle => cexp (Φ (p.1, rep p.2))) (W ×ˢ univ) := by
  rintro ⟨b₀, z₀⟩ ⟨hb₀, -⟩
  have hloc := isLocalDiffeomorph_cexp (rep z₀)
  have hz₀ : z₀ ∈ hloc.localInverse.source := by
    have h := hloc.localInverse_mem_source
    rwa [cexp_rep] at h
  have hS : W ×ˢ hloc.localInverse.source ∈ 𝓝 (b₀, z₀) :=
    (hW.prod hloc.localInverse_open_source).mem_nhds ⟨hb₀, hz₀⟩
  have hin : ContMDiffOn ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      ((SurfaceModel.model F.base.kind).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : F.base.Carrier × Circle => (p.1, hloc.localInverse p.2))
      (W ×ˢ hloc.localInverse.source) :=
    contMDiffOn_fst.prodMk (hloc.contMDiffOn_localInverse.comp contMDiffOn_snd fun p hp => hp.2)
  have hsm : ContMDiffOn ((SurfaceModel.model F.base.kind).prod (𝓡 1)) (𝓡 1) ∞
      (fun p : F.base.Carrier × Circle => cexp (Φ (p.1, hloc.localInverse p.2)))
      (W ×ˢ hloc.localInverse.source) :=
    contMDiff_cexp.comp_contMDiffOn (hΦ.comp hin fun p hp => ⟨hp.1, mem_univ _⟩)
  refine ((hsm.contMDiffAt hS).congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hS] with p hp
  have hcs : cexp (hloc.localInverse p.2) = p.2 := hloc.localInverse_right_inv hp.2
  obtain ⟨n, hn⟩ := cexp_eq_cexp_iff.mp ((cexp_rep p.2).trans hcs.symm)
  change cexp (Φ (p.1, rep p.2)) = cexp (Φ (p.1, hloc.localInverse p.2))
  rw [hn, hper p.1 hp.1, cexp_add_int]

variable (τ₁ τ₂) (O) in
def glueLift (ℓ : F.base.Carrier → ℝ) (p : F.base.Carrier × ℝ) : ℝ :=
  (1 - ℓ p.1) * p.2 + ℓ p.1 * transitionLift τ₁ τ₂ O p

variable (τ₁ τ₂) (O) in
def glueInv (ℓ : F.base.Carrier → ℝ) (p : F.base.Carrier × ℝ) : ℝ :=
  Function.invFun (fun t => glueLift τ₁ τ₂ O ℓ (p.1, t)) p.2

variable (τ₁ τ₂) (O) in
def glueMap (ℓ : F.base.Carrier → ℝ) (p : F.base.Carrier × Circle) : Circle :=
  cexp (glueLift τ₁ τ₂ O ℓ (p.1, rep p.2))

variable (τ₁ τ₂) (O) in
def glueMapInv (ℓ : F.base.Carrier → ℝ) (p : F.base.Carrier × Circle) : Circle :=
  cexp (glueInv τ₁ τ₂ O ℓ (p.1, rep p.2))

section GlueMaps

variable {ℓ : F.base.Carrier → ℝ}
  (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
  (h₁ : τ₁.IsPositive (o.restrictOpen V₁)) (h₂ : τ₂.IsPositive (o.restrictOpen V₂))
  (hcov : V₁ ⊓ V₂ = ⨆ O' ∈ O, O')
  (hdis : (O : Set (TopologicalSpace.Opens F.base.Carrier)).PairwiseDisjoint id)
  (hsc : ∀ O' ∈ O, IsSimplyConnected (O' : Set F.base.Carrier))
  (hℓ : ContMDiff (SurfaceModel.model F.base.kind) 𝓘(ℝ, ℝ) ∞ ℓ)
  (hℓ0 : ∀ b, 0 ≤ ℓ b) (hℓ1 : ∀ b, ℓ b ≤ 1)

include h₁ h₂ hcov hdis hsc in
theorem glueLift_add_one {b : F.base.Carrier} (hb : b ∈ V₁ ⊓ V₂) (t : ℝ) :
    glueLift τ₁ τ₂ O ℓ (b, t + 1) = glueLift τ₁ τ₂ O ℓ (b, t) + 1 := by
  simp only [glueLift]
  rw [transitionLift_add_one o h₁ h₂ hcov hdis hsc hb t]
  ring

include h₁ h₂ hcov hdis hsc in
theorem glueLift_add_int {b : F.base.Carrier} (hb : b ∈ V₁ ⊓ V₂) (t : ℝ) (n : ℤ) :
    glueLift τ₁ τ₂ O ℓ (b, t + n) = glueLift τ₁ τ₂ O ℓ (b, t) + n :=
  add_int_of_add_one (f := fun s => glueLift τ₁ τ₂ O ℓ (b, s))
    (glueLift_add_one o h₁ h₂ hcov hdis hsc hb) t n

include hcov hdis hsc hℓ in
theorem contMDiffOn_glueLift :
    ContMDiffOn ((SurfaceModel.model F.base.kind).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (glueLift τ₁ τ₂ O ℓ)
      (((V₁ ⊓ V₂ : TopologicalSpace.Opens F.base.Carrier) : Set F.base.Carrier) ×ˢ univ) := by
  have hΦ : ContDiff ℝ ∞ (fun v : ℝ × ℝ × ℝ => (1 - v.1) * v.2.1 + v.1 * v.2.2) :=
    ((contDiff_const.sub contDiff_fst).mul (contDiff_fst.comp contDiff_snd)).add
      (contDiff_fst.mul (contDiff_snd.comp contDiff_snd))
  have hin : ContMDiffOn ((SurfaceModel.model F.base.kind).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞
      (fun p : F.base.Carrier × ℝ => (ℓ p.1, p.2, transitionLift τ₁ τ₂ O p))
      (((V₁ ⊓ V₂ : TopologicalSpace.Opens F.base.Carrier) : Set F.base.Carrier) ×ˢ univ) :=
    (hℓ.comp contMDiff_fst).contMDiffOn.prodMk_space
      (contMDiffOn_snd.prodMk_space (contMDiffOn_transitionLift hcov hdis hsc))
  exact hΦ.contMDiff.comp_contMDiffOn hin

include h₁ h₂ hcov hdis hsc hℓ0 hℓ1 in
theorem deriv_glueLift_pos {b : F.base.Carrier} (hb : b ∈ V₁ ⊓ V₂) (t : ℝ) :
    0 < deriv (fun s => glueLift τ₁ τ₂ O ℓ (b, s)) t := by
  have hK := hasDerivAt_slice (V₁ ⊓ V₂).isOpen (contMDiffOn_transitionLift (τ₁ := τ₁)
    (τ₂ := τ₂) hcov hdis hsc) hb t
  have hd : HasDerivAt (fun s => glueLift τ₁ τ₂ O ℓ (b, s))
      ((1 - ℓ b) * 1 + ℓ b * deriv (fun s => transitionLift τ₁ τ₂ O (b, s)) t) t :=
    ((hasDerivAt_id t).const_mul (1 - ℓ b)).add (hK.const_mul (ℓ b))
  rw [hd.deriv]
  have hKp := deriv_transitionLift_pos o h₁ h₂ hcov hdis hsc hb t
  have h0 := hℓ0 b
  have h1 := hℓ1 b
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]
    linarith
  · nlinarith

include h₁ h₂ hcov hdis hsc hℓ0 hℓ1 in
theorem bijective_glueLift {b : F.base.Carrier} (hb : b ∈ V₁ ⊓ V₂) :
    Function.Bijective fun t => glueLift τ₁ τ₂ O ℓ (b, t) :=
  bijective_of_deriv_pos_of_add_int (deriv_glueLift_pos o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hb)
    (glueLift_add_int o h₁ h₂ hcov hdis hsc hb)

include h₁ h₂ hcov hdis hsc hℓ0 hℓ1 in
theorem glueLift_glueInv {b : F.base.Carrier} (hb : b ∈ V₁ ⊓ V₂) (s : ℝ) :
    glueLift τ₁ τ₂ O ℓ (b, glueInv τ₁ τ₂ O ℓ (b, s)) = s :=
  Function.rightInverse_invFun (bijective_glueLift o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hb).2 s

include h₁ h₂ hcov hdis hsc hℓ0 hℓ1 in
theorem glueInv_glueLift {b : F.base.Carrier} (hb : b ∈ V₁ ⊓ V₂) (t : ℝ) :
    glueInv τ₁ τ₂ O ℓ (b, glueLift τ₁ τ₂ O ℓ (b, t)) = t :=
  Function.leftInverse_invFun (bijective_glueLift o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hb).1 t

include h₁ h₂ hcov hdis hsc hℓ hℓ0 hℓ1 in
theorem contMDiffOn_glueInv :
    ContMDiffOn ((SurfaceModel.model F.base.kind).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (glueInv τ₁ τ₂ O ℓ)
      (((V₁ ⊓ V₂ : TopologicalSpace.Opens F.base.Carrier) : Set F.base.Carrier) ×ˢ univ) :=
  contMDiffOn_inverse_param (V₁ ⊓ V₂).isOpen (contMDiffOn_glueLift hcov hdis hsc hℓ)
    (fun b (hb : b ∈ V₁ ⊓ V₂) => (bijective_glueLift o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hb).1)
    (fun b (hb : b ∈ V₁ ⊓ V₂) t => (deriv_glueLift_pos o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hb t).ne')
    (fun b (hb : b ∈ V₁ ⊓ V₂) s => glueLift_glueInv o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hb s)

include h₁ h₂ hcov hdis hsc hℓ0 hℓ1 in
theorem glueInv_add_int {b : F.base.Carrier} (hb : b ∈ V₁ ⊓ V₂) (s : ℝ) (n : ℤ) :
    glueInv τ₁ τ₂ O ℓ (b, s + n) = glueInv τ₁ τ₂ O ℓ (b, s) + n := by
  apply (bijective_glueLift o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hb).1
  simp only
  rw [glueLift_glueInv o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hb,
    glueLift_add_int o h₁ h₂ hcov hdis hsc hb,
    glueLift_glueInv o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hb]

include h₁ h₂ hcov hdis hsc in
theorem glueMap_cexp {b : F.base.Carrier} (hb : b ∈ V₁ ⊓ V₂) (t : ℝ) :
    glueMap τ₁ τ₂ O ℓ (b, cexp t) = cexp (glueLift τ₁ τ₂ O ℓ (b, t)) := by
  obtain ⟨n, hn⟩ := exists_rep_cexp t
  simp only [glueMap]
  rw [hn, glueLift_add_int o h₁ h₂ hcov hdis hsc hb, cexp_add_int]

include h₁ h₂ hcov hdis hsc hℓ0 hℓ1 in
theorem glueMapInv_glueMap {b : F.base.Carrier} (hb : b ∈ V₁ ⊓ V₂) (z : Circle) :
    glueMapInv τ₁ τ₂ O ℓ (b, glueMap τ₁ τ₂ O ℓ (b, z)) = z := by
  obtain ⟨n, hn⟩ := exists_rep_cexp (glueLift τ₁ τ₂ O ℓ (b, rep z))
  simp only [glueMapInv, glueMap]
  rw [hn, glueInv_add_int o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hb,
    glueInv_glueLift o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hb, cexp_add_int, cexp_rep]

include h₁ h₂ hcov hdis hsc hℓ0 hℓ1 in
theorem glueMap_glueMapInv {b : F.base.Carrier} (hb : b ∈ V₁ ⊓ V₂) (w : Circle) :
    glueMap τ₁ τ₂ O ℓ (b, glueMapInv τ₁ τ₂ O ℓ (b, w)) = w := by
  obtain ⟨n, hn⟩ := exists_rep_cexp (glueInv τ₁ τ₂ O ℓ (b, rep w))
  simp only [glueMapInv, glueMap]
  rw [hn, glueLift_add_int o h₁ h₂ hcov hdis hsc hb,
    glueLift_glueInv o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hb, cexp_add_int, cexp_rep]

include h₁ h₂ hcov hdis hsc hℓ in
theorem contMDiffOn_glueMap :
    ContMDiffOn ((SurfaceModel.model F.base.kind).prod (𝓡 1)) (𝓡 1) ∞ (glueMap τ₁ τ₂ O ℓ)
      (((V₁ ⊓ V₂ : TopologicalSpace.Opens F.base.Carrier) : Set F.base.Carrier) ×ˢ univ) :=
  contMDiffOn_cexp_rep (V₁ ⊓ V₂).isOpen (contMDiffOn_glueLift hcov hdis hsc hℓ)
    fun b (hb : b ∈ V₁ ⊓ V₂) t n => glueLift_add_int o h₁ h₂ hcov hdis hsc hb t n

include h₁ h₂ hcov hdis hsc hℓ hℓ0 hℓ1 in
theorem contMDiffOn_glueMapInv :
    ContMDiffOn ((SurfaceModel.model F.base.kind).prod (𝓡 1)) (𝓡 1) ∞ (glueMapInv τ₁ τ₂ O ℓ)
      (((V₁ ⊓ V₂ : TopologicalSpace.Opens F.base.Carrier) : Set F.base.Carrier) ×ˢ univ) :=
  contMDiffOn_cexp_rep (V₁ ⊓ V₂).isOpen (contMDiffOn_glueInv o h₁ h₂ hcov hdis hsc hℓ hℓ0 hℓ1)
    fun b (hb : b ∈ V₁ ⊓ V₂) s n => glueInv_add_int o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hb s n

theorem glueMap_of_zero {b : F.base.Carrier} (h0 : ℓ b = 0) (z : Circle) :
    glueMap τ₁ τ₂ O ℓ (b, z) = z := by
  simp only [glueMap, glueLift, h0, sub_zero, one_mul, zero_mul, add_zero]
  exact cexp_rep z

include h₁ h₂ hcov hdis hsc hℓ0 hℓ1 in
theorem glueMapInv_of_zero {b : F.base.Carrier} (hb : b ∈ V₁ ⊓ V₂) (h0 : ℓ b = 0)
    (w : Circle) : glueMapInv τ₁ τ₂ O ℓ (b, w) = w := by
  have h := glueMap_glueMapInv o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hb w
  rwa [glueMap_of_zero h0] at h

include hcov hdis hsc in
theorem glueMap_of_one {b : F.base.Carrier} (hb : b ∈ V₁ ⊓ V₂) (h1 : ℓ b = 1) (z : Circle) :
    glueMap τ₁ τ₂ O ℓ (b, z) = transitionAngle τ₁ τ₂ b z := by
  simp only [glueMap, glueLift, h1, sub_self, zero_mul, one_mul, zero_add]
  rw [cexp_transitionLift hcov hdis hsc (p := (b, rep z)) hb, cexp_rep]

variable (τ₁ τ₂) (O) (ℓ) in
open scoped Classical in
def glueAngle (x : U) : Circle :=
  if F.projection x ∈ V₁ ⊓ V₂ then glueMap τ₁ τ₂ O ℓ (F.projection x, τ₁.angle x)
  else if F.projection x ∈ V₁ then τ₁.angle x else τ₂.angle x

variable (τ₁ τ₂) (O) (ℓ) in
open scoped Classical in
def glueSymmFn (b : F.base.Carrier) (w : Circle) : U :=
  if b ∈ V₁ ⊓ V₂ then τ₁.symmFn b (glueMapInv τ₁ τ₂ O ℓ (b, w))
  else if b ∈ V₁ then τ₁.symmFn b w else τ₂.symmFn b w

theorem glueAngle_of_mem_inf {x : U} (hx : F.projection x ∈ V₁ ⊓ V₂) :
    glueAngle τ₁ τ₂ O ℓ x = glueMap τ₁ τ₂ O ℓ (F.projection x, τ₁.angle x) := by
  rw [glueAngle, ite_eq_left hx]

theorem glueAngle_of_zero {x : U} (hx : F.projection x ∈ V₁) (h0 : ℓ (F.projection x) = 0) :
    glueAngle τ₁ τ₂ O ℓ x = τ₁.angle x := by
  by_cases h : F.projection x ∈ V₁ ⊓ V₂
  · rw [glueAngle, ite_eq_left h, glueMap_of_zero h0]
  · rw [glueAngle, ite_eq_right h, ite_eq_left hx]

include hcov hdis hsc in
theorem glueAngle_of_one {x : U} (hx : F.projection x ∈ V₂) (h1 : ℓ (F.projection x) = 1) :
    glueAngle τ₁ τ₂ O ℓ x = τ₂.angle x := by
  by_cases h : F.projection x ∈ V₁ ⊓ V₂
  · rw [glueAngle, ite_eq_left h, glueMap_of_one hcov hdis hsc h h1]
    change τ₂.angle (τ₁.symmFn (F.projection x) (τ₁.angle x)) = _
    rw [τ₁.symmFn_angle x h.1]
  · have h' : F.projection x ∉ V₁ := fun h₁' => h ⟨h₁', hx⟩
    rw [glueAngle, ite_eq_right h, ite_eq_right h']

include h₁ h₂ hcov hdis hsc hℓ0 hℓ1 in
theorem glueSymmFn_of_zero {b : F.base.Carrier} (hb : b ∈ V₁) (h0 : ℓ b = 0) (w : Circle) :
    glueSymmFn τ₁ τ₂ O ℓ b w = τ₁.symmFn b w := by
  by_cases h : b ∈ V₁ ⊓ V₂
  · rw [glueSymmFn, ite_eq_left h, glueMapInv_of_zero o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 h h0]
  · rw [glueSymmFn, ite_eq_right h, ite_eq_left hb]

include h₁ h₂ hcov hdis hsc hℓ0 hℓ1 in
theorem glueSymmFn_of_one {b : F.base.Carrier} (hb : b ∈ V₂) (h1 : ℓ b = 1) (w : Circle) :
    glueSymmFn τ₁ τ₂ O ℓ b w = τ₂.symmFn b w := by
  by_cases h : b ∈ V₁ ⊓ V₂
  · rw [glueSymmFn, ite_eq_left h]
    set z := glueMapInv τ₁ τ₂ O ℓ (b, w)
    have hz := glueMap_glueMapInv o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 h w
    rw [glueMap_of_one hcov hdis hsc h h1] at hz
    set y := τ₁.symmFn b z
    have hy : F.projection y = b := τ₁.projection_symmFn b z
    have hy₂ : F.projection y ∈ V₂ := hy ▸ hb
    have h3 := τ₂.symmFn_angle y hy₂
    change τ₂.angle y = w at hz
    rw [hz, hy] at h3
    exact h3.symm
  · have h' : b ∉ V₁ := fun h₁' => h ⟨h₁', hb⟩
    rw [glueSymmFn, ite_eq_right h, ite_eq_right h']

theorem projection_glueSymmFn (b : F.base.Carrier) (w : Circle) :
    F.projection (glueSymmFn τ₁ τ₂ O ℓ b w) = b := by
  unfold glueSymmFn
  split_ifs <;> exact projection_symmFn _ _ _

include h₁ h₂ hcov hdis hsc hℓ0 hℓ1 in
theorem glueAngle_glueSymmFn {b : F.base.Carrier} (hb : b ∈ V₁ ⊔ V₂) (w : Circle) :
    glueAngle τ₁ τ₂ O ℓ (glueSymmFn τ₁ τ₂ O ℓ b w) = w := by
  have hπ := projection_glueSymmFn (τ₁ := τ₁) (τ₂ := τ₂) (O := O) (ℓ := ℓ) b w
  by_cases h : b ∈ V₁ ⊓ V₂
  · have hm : F.projection (glueSymmFn τ₁ τ₂ O ℓ b w) ∈ V₁ ⊓ V₂ := by
      rw [hπ]
      exact h
    rw [glueAngle_of_mem_inf hm, hπ]
    rw [glueSymmFn, ite_eq_left h, τ₁.angle_symmFn h.1]
    exact glueMap_glueMapInv o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 h w
  · by_cases h' : b ∈ V₁
    · have e : glueSymmFn τ₁ τ₂ O ℓ b w = τ₁.symmFn b w := by
        rw [glueSymmFn, ite_eq_right h, ite_eq_left h']
      rw [glueAngle, hπ, ite_eq_right h, ite_eq_left h', e, τ₁.angle_symmFn h']
    · have hb₂ : b ∈ V₂ := (TopologicalSpace.Opens.mem_sup.mp hb).resolve_left h'
      have e : glueSymmFn τ₁ τ₂ O ℓ b w = τ₂.symmFn b w := by
        rw [glueSymmFn, ite_eq_right h, ite_eq_right h']
      rw [glueAngle, hπ, ite_eq_right h, ite_eq_right h', e, τ₂.angle_symmFn hb₂]

include h₁ h₂ hcov hdis hsc hℓ0 hℓ1 in
theorem glueSymmFn_glueAngle (x : U) (hx : F.projection x ∈ V₁ ⊔ V₂) :
    glueSymmFn τ₁ τ₂ O ℓ (F.projection x) (glueAngle τ₁ τ₂ O ℓ x) = x := by
  by_cases h : F.projection x ∈ V₁ ⊓ V₂
  · rw [glueAngle_of_mem_inf h, glueSymmFn, ite_eq_left h,
      glueMapInv_glueMap o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 h, τ₁.symmFn_angle x h.1]
  · by_cases h' : F.projection x ∈ V₁
    · rw [glueAngle, ite_eq_right h, ite_eq_left h', glueSymmFn, ite_eq_right h, ite_eq_left h',
        τ₁.symmFn_angle x h']
    · have hx₂ : F.projection x ∈ V₂ := (TopologicalSpace.Opens.mem_sup.mp hx).resolve_left h'
      rw [glueAngle, ite_eq_right h, ite_eq_right h', glueSymmFn, ite_eq_right h, ite_eq_right h',
        τ₂.symmFn_angle x hx₂]

theorem eventually_zero_and_mem {b : F.base.Carrier} {W : TopologicalSpace.Opens F.base.Carrier}
    (hb : b ∈ W) {c : ℝ} (h : ℓ =ᶠ[𝓝 b] fun _ => c) : ∀ᶠ b' in 𝓝 b, b' ∈ W ∧ ℓ b' = c :=
  Filter.Eventually.and (W.isOpen.mem_nhds hb : ∀ᶠ b' in 𝓝 b, b' ∈ W) h

include h₁ h₂ hcov hdis hsc hℓ in
theorem contMDiffOn_glueAngle (hz : ∀ b ∈ V₁, b ∉ V₂ → ℓ =ᶠ[𝓝 b] 0)
    (hone : ∀ b ∈ V₂, b ∉ V₁ → ℓ =ᶠ[𝓝 b] 1) :
    ContMDiffOn C.model (𝓡 1) ∞ (glueAngle τ₁ τ₂ O ℓ)
      (F.projection ⁻¹' ((V₁ ⊔ V₂ : TopologicalSpace.Opens F.base.Carrier) :
        Set F.base.Carrier)) := by
  intro x hx
  have hx' : F.projection x ∈ V₁ ⊔ V₂ := hx
  refine ContMDiffAt.contMDiffWithinAt ?_
  by_cases h : F.projection x ∈ V₁ ⊓ V₂
  · have hn : F.projection ⁻¹' ((V₁ ⊓ V₂ : TopologicalSpace.Opens F.base.Carrier) :
        Set F.base.Carrier) ∈ 𝓝 x := (isOpen_preimage (V₁ ⊓ V₂)).mem_nhds h
    have hin : ContMDiffAt C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1)) ∞
        (fun y : U => (F.projection y, τ₁.angle y)) x :=
      F.smooth.contMDiffAt.prodMk
        (τ₁.contMDiffOn_angle.contMDiffAt ((isOpen_preimage V₁).mem_nhds h.1))
    have hg : ContMDiffAt ((SurfaceModel.model F.base.kind).prod (𝓡 1)) (𝓡 1) ∞
        (glueMap τ₁ τ₂ O ℓ) (F.projection x, τ₁.angle x) :=
      (contMDiffOn_glueMap o h₁ h₂ hcov hdis hsc hℓ).contMDiffAt
        (((V₁ ⊓ V₂).isOpen.prod isOpen_univ).mem_nhds ⟨h, mem_univ _⟩)
    refine (hg.comp x hin).congr_of_eventuallyEq ?_
    filter_upwards [hn] with y hy
    exact glueAngle_of_mem_inf hy
  · by_cases h' : F.projection x ∈ V₁
    · have hb₂ : F.projection x ∉ V₂ := fun h₂' => h ⟨h', h₂'⟩
      have hev := (F.projection.continuous.continuousAt (x := x)).eventually
        (eventually_zero_and_mem h' (hz _ h' hb₂))
      refine (τ₁.contMDiffOn_angle.contMDiffAt
        ((isOpen_preimage V₁).mem_nhds h')).congr_of_eventuallyEq ?_
      filter_upwards [hev] with y hy
      exact glueAngle_of_zero hy.1 hy.2
    · have hx₂ : F.projection x ∈ V₂ := (TopologicalSpace.Opens.mem_sup.mp hx').resolve_left h'
      have hev := (F.projection.continuous.continuousAt (x := x)).eventually
        (eventually_zero_and_mem hx₂ (hone _ hx₂ h'))
      refine (τ₂.contMDiffOn_angle.contMDiffAt
        ((isOpen_preimage V₂).mem_nhds hx₂)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with y hy
      exact glueAngle_of_one hcov hdis hsc hy.1 hy.2

include h₁ h₂ hcov hdis hsc hℓ hℓ0 hℓ1 in
theorem contMDiffOn_glueSymmFn (hz : ∀ b ∈ V₁, b ∉ V₂ → ℓ =ᶠ[𝓝 b] 0)
    (hone : ∀ b ∈ V₂, b ∉ V₁ → ℓ =ᶠ[𝓝 b] 1) :
    ContMDiffOn ((SurfaceModel.model F.base.kind).prod (𝓡 1)) C.model ∞
      (fun p : F.base.Carrier × Circle => glueSymmFn τ₁ τ₂ O ℓ p.1 p.2)
      (((V₁ ⊔ V₂ : TopologicalSpace.Opens F.base.Carrier) : Set F.base.Carrier) ×ˢ univ) := by
  rintro ⟨b, w⟩ ⟨hb, -⟩
  have hb' : b ∈ V₁ ⊔ V₂ := hb
  refine ContMDiffAt.contMDiffWithinAt ?_
  by_cases h : b ∈ V₁ ⊓ V₂
  · have hn : ((V₁ ⊓ V₂ : TopologicalSpace.Opens F.base.Carrier) : Set F.base.Carrier) ×ˢ
        (univ : Set Circle) ∈ 𝓝 (b, w) :=
      ((V₁ ⊓ V₂).isOpen.prod isOpen_univ).mem_nhds ⟨h, mem_univ _⟩
    have hin : ContMDiffOn ((SurfaceModel.model F.base.kind).prod (𝓡 1))
        ((SurfaceModel.model F.base.kind).prod (𝓡 1)) ∞
        (fun p : F.base.Carrier × Circle => (p.1, glueMapInv τ₁ τ₂ O ℓ p))
        (((V₁ ⊓ V₂ : TopologicalSpace.Opens F.base.Carrier) : Set F.base.Carrier) ×ˢ univ) :=
      contMDiffOn_fst.prodMk (contMDiffOn_glueMapInv o h₁ h₂ hcov hdis hsc hℓ hℓ0 hℓ1)
    have hc := (τ₁.contMDiffOn_symmFn.comp hin fun p hp => ⟨hp.1.1, mem_univ _⟩).contMDiffAt hn
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [hn] with p hp
    change glueSymmFn τ₁ τ₂ O ℓ p.1 p.2 = τ₁.symmFn p.1 (glueMapInv τ₁ τ₂ O ℓ (p.1, p.2))
    rw [glueSymmFn, ite_eq_left (show p.1 ∈ V₁ ⊓ V₂ from hp.1)]
  · by_cases h' : b ∈ V₁
    · have hb₂ : b ∉ V₂ := fun h₂' => h ⟨h', h₂'⟩
      have hev : ∀ᶠ p : F.base.Carrier × Circle in 𝓝 (b, w), p.1 ∈ V₁ ∧ ℓ p.1 = 0 :=
        (continuousAt_fst (p := (b, w))).eventually (eventually_zero_and_mem h' (hz _ h' hb₂))
      refine (τ₁.contMDiffOn_symmFn.contMDiffAt ((V₁.isOpen.prod isOpen_univ).mem_nhds
        ⟨h', mem_univ _⟩)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with p hp
      exact glueSymmFn_of_zero o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hp.1 hp.2 p.2
    · have hb₂ : b ∈ V₂ := (TopologicalSpace.Opens.mem_sup.mp hb').resolve_left h'
      have hev : ∀ᶠ p : F.base.Carrier × Circle in 𝓝 (b, w), p.1 ∈ V₂ ∧ ℓ p.1 = 1 :=
        (continuousAt_fst (p := (b, w))).eventually
          (eventually_zero_and_mem hb₂ (hone _ hb₂ h'))
      refine (τ₂.contMDiffOn_symmFn.contMDiffAt ((V₂.isOpen.prod isOpen_univ).mem_nhds
        ⟨hb₂, mem_univ _⟩)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with p hp
      exact glueSymmFn_of_one o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hp.1 hp.2 p.2

include h₁ h₂ hcov hdis hsc hℓ hℓ0 hℓ1 in
theorem exists_glued (hz : ∀ b ∈ V₁, b ∉ V₂ → ℓ =ᶠ[𝓝 b] 0)
    (hone : ∀ b ∈ V₂, b ∉ V₁ → ℓ =ᶠ[𝓝 b] 1) :
    ∃ τ : FibreCoordinate F (V₁ ⊔ V₂),
      (∀ x : U, F.projection x ∈ V₁ ⊔ V₂ → τ.angle x = glueAngle τ₁ τ₂ O ℓ x) ∧
      ∀ q : (V₁ ⊔ V₂ : TopologicalSpace.Opens F.base.Carrier) × Circle,
        (τ.toDiffeo.symm q).val = glueSymmFn τ₁ τ₂ O ℓ q.1.val q.2 := by
  have hσ : ContMDiff ((SurfaceModel.model F.base.kind).prod (𝓡 1)) C.model ∞
      (fun q : (V₁ ⊔ V₂ : TopologicalSpace.Opens F.base.Carrier) × Circle =>
        glueSymmFn τ₁ τ₂ O ℓ q.1.val q.2) :=
    (contMDiffOn_glueSymmFn o h₁ h₂ hcov hdis hsc hℓ hℓ0 hℓ1 hz hone).comp_contMDiff
      ((contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd)
      fun q => ⟨q.1.2, mem_univ _⟩
  refine ⟨ofAngle (V₁ ⊔ V₂) (glueAngle τ₁ τ₂ O ℓ)
    (fun q => glueSymmFn τ₁ τ₂ O ℓ q.1.val q.2)
    (contMDiffOn_glueAngle o h₁ h₂ hcov hdis hsc hℓ hz hone) hσ
    (fun q => projection_glueSymmFn q.1.val q.2)
    (fun q => glueAngle_glueSymmFn o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 q.1.2 q.2)
    (fun x hx => glueSymmFn_glueAngle o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 x hx),
    fun x hx => angle_ofAngle _ _ _ _ _ _ _ _ x hx, fun q => rfl⟩

end GlueMaps

theorem glue (τ₁ : FibreCoordinate F V₁) (τ₂ : FibreCoordinate F V₂)
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
    (h₁ : τ₁.IsPositive (o.restrictOpen V₁)) (h₂ : τ₂.IsPositive (o.restrictOpen V₂))
    (ℓ : F.base.Carrier → ℝ) (hℓ : ContMDiff (SurfaceModel.model F.base.kind) 𝓘(ℝ, ℝ) ∞ ℓ)
    (hℓ01 : ∀ b, 0 ≤ ℓ b ∧ ℓ b ≤ 1)
    (h₀ : ∀ b ∈ V₁, b ∉ V₂ → ℓ =ᶠ[𝓝 b] 0) (h₁' : ∀ b ∈ V₂, b ∉ V₁ → ℓ =ᶠ[𝓝 b] 1)
    (hO : ∃ O : Finset (TopologicalSpace.Opens F.base.Carrier), V₁ ⊓ V₂ = ⨆ O' ∈ O, O' ∧
      (O : Set (TopologicalSpace.Opens F.base.Carrier)).PairwiseDisjoint id ∧
      ∀ O' ∈ O, IsSimplyConnected (O' : Set F.base.Carrier)) :
    ∃ τ : FibreCoordinate F (V₁ ⊔ V₂), τ.IsPositive (o.restrictOpen (V₁ ⊔ V₂)) ∧
      (∀ x : U, ℓ (F.projection x) = 0 → F.projection x ∈ V₁ → τ.angle x = τ₁.angle x) ∧
      (∀ x : U, ℓ (F.projection x) = 1 → F.projection x ∈ V₂ → τ.angle x = τ₂.angle x) ∧
      (∀ q : (V₁ ⊔ V₂ : TopologicalSpace.Opens F.base.Carrier) × Circle,
        ℓ q.1.val = 0 → q.1.val ∈ V₁ → (τ.toDiffeo.symm q).val = τ₁.symmFn q.1.val q.2) ∧
      (∀ q : (V₁ ⊔ V₂ : TopologicalSpace.Opens F.base.Carrier) × Circle,
        ℓ q.1.val = 1 → q.1.val ∈ V₂ → (τ.toDiffeo.symm q).val = τ₂.symmFn q.1.val q.2) := by
  obtain ⟨O, hcov, hdis, hsc⟩ := hO
  have hℓ0 : ∀ b, 0 ≤ ℓ b := fun b => (hℓ01 b).1
  have hℓ1 : ∀ b, ℓ b ≤ 1 := fun b => (hℓ01 b).2
  obtain ⟨τ, hτθ, hτσ⟩ := exists_glued (τ₁ := τ₁) (τ₂ := τ₂) (O := O) (ℓ := ℓ) o h₁ h₂ hcov hdis
    hsc hℓ hℓ0 hℓ1 h₀ h₁'
  have hsup₁ : ∀ {b : F.base.Carrier}, b ∈ V₁ → b ∈ V₁ ⊔ V₂ := fun hb =>
    TopologicalSpace.Opens.mem_sup.mpr (Or.inl hb)
  have hsup₂ : ∀ {b : F.base.Carrier}, b ∈ V₂ → b ∈ V₁ ⊔ V₂ := fun hb =>
    TopologicalSpace.Opens.mem_sup.mpr (Or.inr hb)
  refine ⟨τ, ?_, fun x h0 hx => ?_, fun x h1 hx => ?_, fun q h0 hq => ?_, fun q h1 hq => ?_⟩
  · refine τ.isPositive_of_ambient o fun x hx L hL => ?_
    by_cases h : F.projection x ∈ V₁ ⊓ V₂
    · have hθ : ∀ᶠ y in 𝓝 x, τ.angle y = glueMap τ₁ τ₂ O ℓ (F.projection y, τ₁.angle y) := by
        filter_upwards [(isOpen_preimage (V₁ ⊓ V₂)).mem_nhds h] with y hy
        rw [hτθ y (hsup₁ hy.1), glueAngle_of_mem_inf hy]
      have hh : MDifferentiableAt ((SurfaceModel.model F.base.kind).prod (𝓡 1)) (𝓡 1)
          (glueMap τ₁ τ₂ O ℓ) (F.projection x, τ₁.angle x) :=
        ((contMDiffOn_glueMap o h₁ h₂ hcov hdis hsc hℓ).contMDiffAt
          (((V₁ ⊓ V₂).isOpen.prod isOpen_univ).mem_nhds ⟨h, mem_univ _⟩)).mdifferentiableAt
            (by simp)
      have hz : τ₁.angle x = cexp (rep (τ₁.angle x)) := (cexp_rep _).symm
      have hG := hasDerivAt_slice (V₁ ⊓ V₂).isOpen (contMDiffOn_glueLift (τ₁ := τ₁)
        (τ₂ := τ₂) hcov hdis hsc hℓ) h (rep (τ₁.angle x))
      have hlift : (fun t => glueMap τ₁ τ₂ O ℓ (F.projection x, cexp t)) =ᶠ[𝓝 (rep (τ₁.angle x))]
          fun t => cexp (glueLift τ₁ τ₂ O ℓ (F.projection x, t)) :=
        Filter.Eventually.of_forall fun t => glueMap_cexp o h₁ h₂ hcov hdis hsc h t
      obtain ⟨-, hpos, -⟩ := orientation_map_fibrewise_lift o τ₁ h₁ h.1 hθ hh hz hG hlift L hL
      rw [hpos (deriv_glueLift_pos o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 h _), hτθ x hx,
        glueAngle_of_mem_inf h, ← glueMap_cexp o h₁ h₂ hcov hdis hsc h, ← hz]
    · by_cases h' : F.projection x ∈ V₁
      · have hb₂ : F.projection x ∉ V₂ := fun h₂' => h ⟨h', h₂'⟩
        have hθ : τ.angle =ᶠ[𝓝 x] τ₁.angle := by
          filter_upwards [(F.projection.continuous.continuousAt (x := x)).eventually
            (eventually_zero_and_mem h' (h₀ _ h' hb₂))] with y hy
          rw [hτθ y (hsup₁ hy.1), glueAngle_of_zero hy.1 hy.2]
        exact orientation_map_of_angle_eventuallyEq o τ₁ h₁ h' hθ L hL
      · have hx₂ : F.projection x ∈ V₂ :=
          (TopologicalSpace.Opens.mem_sup.mp hx).resolve_left h'
        have hθ : τ.angle =ᶠ[𝓝 x] τ₂.angle := by
          filter_upwards [(F.projection.continuous.continuousAt (x := x)).eventually
            (eventually_zero_and_mem hx₂ (h₁' _ hx₂ h'))] with y hy
          rw [hτθ y (hsup₂ hy.1), glueAngle_of_one hcov hdis hsc hy.1 hy.2]
        exact orientation_map_of_angle_eventuallyEq o τ₂ h₂ hx₂ hθ L hL
  · rw [hτθ x (hsup₁ hx), glueAngle_of_zero hx h0]
  · rw [hτθ x (hsup₂ hx), glueAngle_of_one hcov hdis hsc hx h1]
  · rw [hτσ, glueSymmFn_of_zero o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hq h0]
  · rw [hτσ, glueSymmFn_of_one o h₁ h₂ hcov hdis hsc hℓ0 hℓ1 hq h1]

end FibreCoordinate

end Glue


end GC.Seifert
