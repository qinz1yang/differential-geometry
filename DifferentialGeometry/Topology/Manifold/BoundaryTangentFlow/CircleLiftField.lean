import DifferentialGeometry.Topology.Manifold.BoundaryTangentFlow.Tangency
import DifferentialGeometry.Topology.Ehresmann.CircleFibreTransport
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Lifting the rotation of the circle along a boundary submersion

For a smooth submersion `p : M → S¹` of a manifold with boundary (model `𝓡∂ (n + 1)`) whose restriction
to the boundary is still a submersion (curve form), there is a smooth vector field `X` on `M`,
tangent to `∂M` (curve form), with `dp (X q)` equal to the velocity of the rotation `t ↦ e^{it} p q`
at `t = 0` (`exists_circleLiftField`).

Route: a local angle `θ` with `Circle.exp ∘ θ = p` (`exists_local_angle`, from
`Ehresmann/CircleFibreTransport.lean:94`); near each point a field `X = (dθ s)⁻¹ s` for a section
`s` that is constant in the tangent-bundle trivialization at the point, chosen tangent to the boundary
hyperplane at boundary points (`exists_local_circleLiftField`); the conditions `dp X = rotation` and
"normal coordinate `0` at boundary points" are affine, so the local fields glue by Mathlib's
`exists_contMDiffSection_forall_mem_convex_of_local`; the curve form of tangency comes from
`BoundaryTangentFlow/Tangency.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.BoundaryTangentFlow

open DifferentialGeometry.Manifold.BoundaryCollar
open DifferentialGeometry.Topology.Ehresmann.CircleFibre

/-- The circle diffeomorphism `AddCircle 1 ≃ S¹` on a real number. -/
theorem diffeomorphCircle_coe_eq_circleExp (t : ℝ) :
    AddCircle.diffeomorphCircle (t : AddCircle (1 : ℝ)) = Circle.exp (2 * Real.pi * t) := by
  change AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero (t : AddCircle (1 : ℝ)) = _
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  congr 1
  ring

section Angle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

/-- **Local angle.** A smooth map `p : M → S¹` has, near any point, a smooth real lift through
`Circle.exp`; the lift is globally smooth (cut off away from the point). -/
theorem exists_local_angle (p : M → Circle) (hp : ContMDiff I (𝓡 1) ∞ p) (q₀ : M) :
    ∃ θ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ θ ∧ ∀ᶠ q in 𝓝 q₀, Circle.exp (θ q) = p q := by
  let d := AddCircle.diffeomorphCircle
  let a : AddCircle (1 : ℝ) := d.symm (p q₀)
  let α : ℝ := angleLift 0 a - 1 / 2
  have hα : a ≠ (α : AddCircle (1 : ℝ)) := by
    have h := coe_ne_of_mem_Ioo (α := α) (x := angleLift 0 a)
      ⟨by simp only [α]; linarith, by simp only [α]; linarith⟩
    rwa [coe_angleLift] at h
  let θ₀ : M → ℝ := fun q => 2 * Real.pi * angleLift α (d.symm (p q))
  let N : Set M := {q | d.symm (p q) ≠ (α : AddCircle (1 : ℝ))}
  have hdp : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => d.symm (p q)) := d.symm.contMDiff.comp hp
  have hN : IsOpen N := isOpen_ne_fun hdp.continuous continuous_const
  have hq₀N : q₀ ∈ N := hα
  have hθ₀ : ∀ q ∈ N, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ θ₀ q := by
    intro q hq
    have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q => angleLift α (d.symm (p q))) q :=
      ContMDiffAt.comp (g := angleLift α) q (contMDiffAt_angleLift hq) hdp.contMDiffAt
    exact ContMDiffAt.comp (g := fun x : ℝ => 2 * Real.pi * x) q
      (contDiff_const.mul contDiff_id).contMDiff.contMDiffAt h1
  have hexp : ∀ q, Circle.exp (θ₀ q) = p q := by
    intro q
    change Circle.exp (2 * Real.pi * angleLift α (d.symm (p q))) = p q
    rw [← diffeomorphCircle_coe_eq_circleExp, coe_angleLift]
    exact d.apply_symm_apply (p q)
  obtain ⟨f, -, hf⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) q₀).mem_iff.mp (hN.mem_nhds hq₀N)
  refine ⟨fun q => f q • θ₀ q, ?_, ?_⟩
  · apply contMDiff_of_tsupport
    intro x hx
    have hxf : x ∈ tsupport f := tsupport_smul_subset_left _ _ hx
    exact f.contMDiff.contMDiffAt.smul (hθ₀ x (hf hxf))
  · filter_upwards [f.eventuallyEq_one] with q hq
    rw [hq, Pi.one_apply, one_smul]
    exact hexp q

end Angle

section CircleDerivative

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The rotation velocity at `Circle.exp c` is the derivative of `Circle.exp` at `c`. -/
theorem mfderiv_rotation_circleExp_apply_one (c : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun t : ℝ => Circle.exp t * Circle.exp c) 0 1 :
        EuclideanSpace ℝ (Fin 1)) =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp c 1 := by
  have hfun : (fun t : ℝ => Circle.exp t * Circle.exp c) =
      Circle.exp ∘ (fun t : ℝ => t + c) := by
    funext t
    simp only [Function.comp_apply, Circle.exp_add]
  rw [hfun]
  have hexp : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp ((0 : ℝ) + c)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp c) := by
    rw [zero_add]
    exact ((contMDiff_circleExp (m := 1)).mdifferentiableAt (x := c) one_ne_zero).hasMFDerivAt
  have hadd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) 0 (ContinuousLinearMap.id ℝ ℝ) :=
    ((hasFDerivAt_id (0 : ℝ)).add_const c).hasMFDerivAt
  have hcomp := hexp.comp (0 : ℝ) hadd
  exact congrArg (fun L => L 1) hcomp.mfderiv

/-- Through a local angle `θ` (`p = Circle.exp ∘ θ` near `y`), `dp = d(Circle.exp) ∘ dθ`. -/
theorem mfderiv_apply_eq_of_local_angle {p : M → Circle} {θ : M → ℝ} {y : M}
    (hθ : MDifferentiableAt I 𝓘(ℝ, ℝ) θ y) (hpθ : p =ᶠ[𝓝 y] fun q => Circle.exp (θ q))
    (v : TangentSpace I y) :
    (mfderiv I (𝓡 1) p y v : EuclideanSpace ℝ (Fin 1)) =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp (θ y) (mfderiv I 𝓘(ℝ, ℝ) θ y v) := by
  have hexp : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp (θ y) :=
    (contMDiff_circleExp (m := 1)).mdifferentiableAt one_ne_zero
  have h1 : mfderiv I (𝓡 1) p y = mfderiv I (𝓡 1) (Circle.exp ∘ θ) y := hpθ.mfderiv_eq
  rw [h1, mfderiv_comp y hexp hθ]
  rfl

/-- The rotation velocity at `z = Circle.exp c` is `d(Circle.exp)` at `c` on `1`. -/
theorem mfderiv_rotation_apply_one_of_eq {z : Circle} {c : ℝ} (hz : z = Circle.exp c) :
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun t : ℝ => Circle.exp t * z) 0 1 :
        EuclideanSpace ℝ (Fin 1)) =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp c 1 := by
  rw [hz]
  exact mfderiv_rotation_circleExp_apply_one c

end CircleDerivative

/-- An affine condition together with a conditional linear one cuts out a convex set. -/
theorem convex_setOf_eq_and_imp_eq_zero {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W) (r : W) (ℓ : V →ₗ[ℝ] ℝ) (P : Prop) :
    Convex ℝ {v | L v = r ∧ (P → ℓ v = 0)} := by
  intro v hv u hu a b _ _ hab
  refine ⟨?_, fun hP => ?_⟩
  · rw [map_add, map_smul, map_smul, hv.1, hu.1, ← add_smul, hab, one_smul]
  · rw [map_add, map_smul, map_smul, hv.2 hP, hu.2 hP, smul_zero, smul_zero, add_zero]

section Local

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M]

/-- **Local lift field.** Near every point there is a smooth local field `X` with
`dp (X q)` = the rotation velocity at `p q`, whose normal coordinate vanishes at boundary points. -/
theorem exists_local_circleLiftField (p : M → Circle) (hp : ContMDiff (𝓡∂ (n + 1)) (𝓡 1) ∞ p)
    (hsub : ∀ q, Surjective (mfderiv (𝓡∂ (n + 1)) (𝓡 1) p q))
    (hbd : ∀ q, (𝓡∂ (n + 1)).IsBoundaryPoint q → ∃ γ : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) ∞ γ ∧ γ 0 = q ∧
        (∀ t, (𝓡∂ (n + 1)).IsBoundaryPoint (γ t)) ∧
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (p ∘ γ) 0 ≠ 0) (q₀ : M) :
    ∃ U ∈ 𝓝 q₀, ∃ X : (q : M) → TangentSpace (𝓡∂ (n + 1)) q,
      ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
        (fun q => (⟨q, X q⟩ : TangentBundle (𝓡∂ (n + 1)) M)) U ∧
      ∀ q ∈ U, (mfderiv (𝓡∂ (n + 1)) (𝓡 1) p q (X q) : EuclideanSpace ℝ (Fin 1)) =
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun t : ℝ => Circle.exp t * p q) 0 1 :
            EuclideanSpace ℝ (Fin 1)) ∧
        ((𝓡∂ (n + 1)).IsBoundaryPoint q →
          EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))
            (X q : EuclideanSpace ℝ (Fin (n + 1))) = 0) := by
  classical
  let I := 𝓡∂ (n + 1)
  let F := EuclideanSpace ℝ (Fin (n + 1))
  obtain ⟨θ, hθ, hθp⟩ := exists_local_angle (I := I) p hp q₀
  let N₁ : Set M := interior {q | Circle.exp (θ q) = p q}
  have hN₁ : IsOpen N₁ := isOpen_interior
  have hq₀N₁ : q₀ ∈ N₁ := mem_interior_iff_mem_nhds.mpr hθp
  have hpθ : ∀ y ∈ N₁, p =ᶠ[𝓝 y] fun q => Circle.exp (θ q) := by
    intro y hy
    filter_upwards [mem_interior_iff_mem_nhds.mp hy] with q hq using hq.symm
  have hderiv : ∀ y ∈ N₁, ∀ v : TangentSpace I y,
      (mfderiv I (𝓡 1) p y v : EuclideanSpace ℝ (Fin 1)) =
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp (θ y) (mfderiv I 𝓘(ℝ, ℝ) θ y v) := fun y hy v =>
    mfderiv_apply_eq_of_local_angle ((hθ y).mdifferentiableAt (by simp)) (hpθ y hy) v
  -- the seed vector at `q₀`
  obtain ⟨w, hw, hwb⟩ : ∃ w : TangentSpace I q₀, mfderiv I 𝓘(ℝ, ℝ) θ q₀ w ≠ 0 ∧
      (I.IsBoundaryPoint q₀ → EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)) w = 0) := by
    by_cases hb : I.IsBoundaryPoint q₀
    · obtain ⟨γ, hγ, hγ0, hγb, hγp⟩ := hbd q₀ hb
      subst hγ0
      refine ⟨mfderiv 𝓘(ℝ, ℝ) I γ 0 1, ?_,
        fun _ => proj_zero_mfderiv_eq_zero_of_boundary_curve hγ hγb⟩
      intro hzero
      apply hγp
      rw [mfderiv_comp (0 : ℝ) ((hp (γ 0)).mdifferentiableAt (by simp))
        ((hγ 0).mdifferentiableAt (by simp))]
      apply ContinuousLinearMap.ext_ring
      have h := hderiv (γ 0) hq₀N₁ (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)
      rw [hzero, map_zero] at h
      exact h
    · obtain ⟨w, hw⟩ : ∃ w : TangentSpace I q₀, mfderiv I 𝓘(ℝ, ℝ) θ q₀ w ≠ 0 := by
        by_contra hcon
        push Not at hcon
        obtain ⟨u, hu⟩ := hsub q₀ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
        have h := hderiv q₀ hq₀N₁ u
        rw [hcon u, map_zero] at h
        have h0 : (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0 = (0 : ℝ) :=
          congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) (hu.symm.trans h)
        simp at h0
      exact ⟨w, hw, fun h => absurd h hb⟩
  -- a section that is constant in the trivialization at `q₀`
  let e := trivializationAt F (TangentSpace I : M → Type _) q₀
  have hq₀base : q₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' q₀
  obtain ⟨v, hvdef⟩ : ∃ v : F, v = (e (⟨q₀, w⟩ : TangentBundle I M)).2 := ⟨_, rfl⟩
  let s : (y : M) → TangentSpace I y := fun y => e.symm y v
  have hsq₀ : s q₀ = w := by
    change e.symm q₀ v = w
    rw [hvdef]
    exact e.symm_apply_apply_mk hq₀base w
  have hs : ContMDiffOn I I.tangent ∞ (fun y => (⟨y, s y⟩ : TangentBundle I M)) e.baseSet := by
    apply e.contMDiffOn_section_baseSet_iff.mpr
    apply (contMDiffOn_const (c := v)).congr
    intro y hy
    change (e (⟨y, e.symm y v⟩ : TangentBundle I M)).2 = v
    rw [e.apply_mk_symm hy v]
  have hbase : e.baseSet = (chartAt (EuclideanHalfSpace (n + 1)) q₀).source :=
    TangentBundle.trivializationAt_baseSet q₀
  have hscoord : ∀ y ∈ e.baseSet,
      mfderiv I 𝓘(ℝ, F) (extChartAt I q₀) y (s y) = v := by
    intro y hy
    have h1 := TangentBundle.continuousLinearMapAt_trivializationAt (I := I) (x₀ := q₀)
      (hbase ▸ hy)
    exact (congrArg (fun L => L (s y)) h1).symm.trans
      ((Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy (s y)).trans
        (congrArg Prod.snd (e.apply_mk_symm hy v)))
  have hv0 : EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)) v =
      EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)) w := by
    have h := hscoord q₀ hq₀base
    rw [hsq₀, mfderiv_extChartAt_self] at h
    rw [← h]
    rfl
  let a : M → ℝ := fun y => mfderiv I 𝓘(ℝ, ℝ) θ y (s y)
  have ha : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ a e.baseSet := by
    intro y hy
    exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).contMDiffAt.comp_contMDiffWithinAt y
      ((hθ.contMDiff_tangentMap (by simp)).contMDiffAt.comp_contMDiffWithinAt y (hs y hy))
  have haq₀ : a q₀ ≠ 0 := by
    change mfderiv I 𝓘(ℝ, ℝ) θ q₀ (s q₀) ≠ 0
    rw [hsq₀]
    exact hw
  -- away from the boundary when `q₀` is interior
  obtain ⟨Z, hZ, hq₀Z, hZb⟩ : ∃ Z : Set M, IsOpen Z ∧ q₀ ∈ Z ∧
      ∀ y ∈ Z, I.IsBoundaryPoint y → I.IsBoundaryPoint q₀ := by
    by_cases hb : I.IsBoundaryPoint q₀
    · exact ⟨univ, isOpen_univ, mem_univ _, fun _ _ _ => hb⟩
    · refine ⟨(chartAt (EuclideanHalfSpace (n + 1)) q₀).source ∩
          chartHeight (n := n + 1) q₀ ⁻¹' Ioi 0,
        (contMDiffOn_chartHeight (n := n + 1) (k := ∞) q₀).continuousOn.isOpen_inter_preimage
          (chartAt (EuclideanHalfSpace (n + 1)) q₀).open_source isOpen_Ioi,
        ⟨mem_chart_source _ q₀, ?_⟩, ?_⟩
      · have hne : chartHeight (n := n + 1) q₀ q₀ ≠ 0 := fun h =>
          hb ((chartHeight_eq_zero_iff (n := n + 1) q₀ (mem_chart_source _ q₀)).mp h)
        exact lt_of_le_of_ne (chartHeight_nonneg (n := n + 1) q₀ q₀) hne.symm
      · intro y hy hyb
        have h0 := (chartHeight_eq_zero_iff (n := n + 1) q₀ hy.1).mpr hyb
        have hpos : 0 < chartHeight (n := n + 1) q₀ y := hy.2
        exact absurd h0 hpos.ne'
  let U : Set M := ({y | y ∈ e.baseSet ∧ a y ≠ 0} ∩ N₁) ∩ Z
  have hUa : U ⊆ e.baseSet := fun _ hy => hy.1.1.1
  have hUopen : IsOpen U := by
    refine ((?_ : IsOpen {y | y ∈ e.baseSet ∧ a y ≠ 0}).inter hN₁).inter hZ
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    exact Filter.inter_mem (e.open_baseSet.mem_nhds hy.1)
      ((ha.contMDiffAt (e.open_baseSet.mem_nhds hy.1)).continuousAt.eventually_ne hy.2)
  have hq₀U : q₀ ∈ U := ⟨⟨⟨hq₀base, haq₀⟩, hq₀N₁⟩, hq₀Z⟩
  let X : (y : M) → TangentSpace I y := fun y => (a y)⁻¹ • s y
  refine ⟨U, hUopen.mem_nhds hq₀U, X, ?_, ?_⟩
  · exact ((ha.mono hUa).inv₀ (fun _ hy => hy.1.1.2)).smul_section (hs.mono hUa)
  · intro y hy
    have hθX : mfderiv I 𝓘(ℝ, ℝ) θ y (X y) = 1 := by
      change mfderiv I 𝓘(ℝ, ℝ) θ y ((a y)⁻¹ • s y) = 1
      rw [map_smul]
      exact inv_mul_cancel₀ hy.1.1.2
    refine ⟨?_, ?_⟩
    · have h1 := hderiv y hy.1.2 (X y)
      rw [hθX] at h1
      have hmem : y ∈ {q | Circle.exp (θ q) = p q} := interior_subset hy.1.2
      have h2 := mfderiv_rotation_apply_one_of_eq (z := p y) (c := θ y)
        (show Circle.exp (θ y) = p y from hmem).symm
      exact h1.trans h2.symm
    · intro hyb
      have hq₀b := hZb y hy.2 hyb
      have hy' : y ∈ (chartAt (EuclideanHalfSpace (n + 1)) q₀).source := hbase ▸ hUa hy
      have hs0 : EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)) (s y) = 0 := by
        apply (proj_zero_mfderiv_extChartAt_eq_zero_iff q₀ hy' hyb (v := s y)).mp
        rw [hscoord y (hUa hy), hv0]
        exact hwb hq₀b
      have h := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))).map_smul (a y)⁻¹ (s y : F)
      rw [hs0, smul_zero] at h
      exact h

/-- **Lift field (general dimension).** A smooth submersion `p : M → S¹` of a σ-compact manifold with
boundary which is still a submersion on the boundary (curve form) has a smooth lift field of the
rotation, tangent to the boundary (curve form). -/
theorem exists_circleLiftField [SigmaCompactSpace M] (p : M → Circle)
    (hp : ContMDiff (𝓡∂ (n + 1)) (𝓡 1) ∞ p)
    (hsub : ∀ q, Surjective (mfderiv (𝓡∂ (n + 1)) (𝓡 1) p q))
    (hbd : ∀ q, (𝓡∂ (n + 1)).IsBoundaryPoint q → ∃ γ : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) ∞ γ ∧ γ 0 = q ∧
        (∀ t, (𝓡∂ (n + 1)).IsBoundaryPoint (γ t)) ∧
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (p ∘ γ) 0 ≠ 0) :
    ∃ X : (q : M) → TangentSpace (𝓡∂ (n + 1)) q,
      ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
        (fun q => (⟨q, X q⟩ : TangentBundle (𝓡∂ (n + 1)) M)) ∧
      (∀ q, (𝓡∂ (n + 1)).IsBoundaryPoint q → ∃ γ : ℝ → M,
        ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) ∞ γ ∧ γ 0 = q ∧
          (∀ t, (𝓡∂ (n + 1)).IsBoundaryPoint (γ t)) ∧
          mfderiv 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) γ 0 1 = X q) ∧
      ∀ q, mfderiv (𝓡∂ (n + 1)) (𝓡 1) p q (X q) =
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun t : ℝ => Circle.exp t * p q) 0 1 := by
  let I := 𝓡∂ (n + 1)
  let t : (q : M) → Set (TangentSpace I q) := fun q =>
    {v | (mfderiv I (𝓡 1) p q v : EuclideanSpace ℝ (Fin 1)) =
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun t : ℝ => Circle.exp t * p q) 0 1 :
          EuclideanSpace ℝ (Fin 1)) ∧
      (I.IsBoundaryPoint q → EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))
        (v : EuclideanSpace ℝ (Fin (n + 1))) = 0)}
  have ht : ∀ q, Convex ℝ (t q) := fun q =>
    convex_setOf_eq_and_imp_eq_zero (mfderiv I (𝓡 1) p q).toLinearMap
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun t : ℝ => Circle.exp t * p q) 0 1)
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))).toLinearMap (I.IsBoundaryPoint q)
  obtain ⟨X, hX⟩ := exists_contMDiffSection_forall_mem_convex_of_local I (n := ⊤)
    (TangentSpace I : M → Type _) t ht
    (fun q₀ => exists_local_circleLiftField p hp hsub hbd q₀)
  refine ⟨X, X.contMDiff, ?_, fun q => (hX q).1⟩
  intro q hq
  exact exists_boundary_curve_of_proj_zero hq (X q) ((hX q).2 hq)

end Local

end DifferentialGeometry.Manifold.BoundaryTangentFlow
