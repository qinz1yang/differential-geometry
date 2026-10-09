import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorField.Pullback
import DifferentialGeometry.Topology.Manifold.OrientationCoverComponents
import DifferentialGeometry.Topology.Manifold.OrientationCoverOriented
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.ModelHomeomorph
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle
import DifferentialGeometry.Topology.Flow.Circle

/-!
# Compact connected one-manifolds are circles

Every compact connected boundaryless smooth one-manifold `F` (model `J : ModelWithCorners ℝ E H`
with `finrank ℝ E = 1`) is diffeomorphic to `Circle`:
`nonempty_circle_diffeomorph_of_finrank_eq_one` has exactly the shape of
`GC.Seifert.CircleClassification`.

Route. In a line `V` a vector `w` is positive for `o : Orientation ℝ V (Fin 1)` when some basis
`b` has `b 0 = w` and `b.orientation = o`; positive vectors form a convex set
(`convex_basis_orientation`). The convex local-to-global principle for sections then turns a
compatible orientation into a smooth positive, hence nowhere vanishing, vector field
(`exists_positive_vectorField`).

Orientability (`not_connectedSpace_tangentOrientationCover`). Suppose the orientation double
cover `N` of a compact one-manifold `M` (model `𝓘(ℝ, E)`) is connected. Let `v` be a positive
field for the canonical orientation of `N` and `τ` the deck involution, which reverses that
orientation. Then `u = v - τ^* v` is a smooth nowhere vanishing field with `dτ (u z) = -u (τ z)`.
Its flow `ψ` satisfies `τ (ψ z (-t)) = ψ (τ z) t`; the orbit of `z` is open, so it is all of `N`,
whence `τ z = ψ z s` for some `s`, and `ψ z (s / 2)` is a fixed point of `τ`, which is
impossible. Hence `M` carries a compatible orientation and a nowhere vanishing vector field, and
the flow theorem `exists_addCircle_diffeomorph_of_nonvanishing_vectorField` identifies `M` with
`AddCircle 1`, hence with `Circle`. A general boundaryless model `J` is reduced to `𝓘(ℝ, E)`
through `J.toHomeomorph`.
-/

set_option autoImplicit false

noncomputable section

open Module Bundle Set
open scoped Manifold ContDiff Topology

universe uE uH uM

namespace DifferentialGeometry.Topology.Manifold.OneManifold

section LinearAlgebra

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem eq_repr_smul_basis_zero (b : Basis (Fin 1) ℝ V) (w : V) :
    w = b.repr w 0 • b 0 := by
  conv_lhs => rw [← b.sum_repr w]
  simp

theorem exists_basis_orientation_eq [FiniteDimensional ℝ V] (h : finrank ℝ V = 1)
    (o : Orientation ℝ V (Fin 1)) : ∃ b : Basis (Fin 1) ℝ V, b.orientation = o := by
  let b₀ : Basis (Fin 1) ℝ V := Module.finBasisOfFinrankEq ℝ V h
  rcases b₀.orientation_eq_or_eq_neg o with h₀ | h₀
  · exact ⟨b₀, h₀.symm⟩
  · refine ⟨b₀.unitsSMul (Function.const (Fin 1) (-1)), ?_⟩
    rw [Basis.orientation_unitsSMul, h₀]
    simp

theorem basis_orientation_smul (b : Basis (Fin 1) ℝ V) {r : ℝ} (hr : 0 < r) :
    ∃ b' : Basis (Fin 1) ℝ V, b' 0 = r • b 0 ∧ b'.orientation = b.orientation := by
  refine ⟨b.unitsSMul (Function.const (Fin 1) (Units.mk0 r hr.ne')), ?_, ?_⟩
  · rw [Basis.unitsSMul_apply]
    rfl
  rw [Basis.orientation_unitsSMul, units_smul_eq_self_iff]
  simpa using hr

theorem convex_basis_orientation (o : Orientation ℝ V (Fin 1)) :
    Convex ℝ {w : V | ∃ b : Basis (Fin 1) ℝ V, b 0 = w ∧ b.orientation = o} := by
  rintro w₁ ⟨b₁, rfl, h₁⟩ w₂ ⟨b₂, rfl, h₂⟩ a c ha hc hac
  set r := b₁.repr (b₂ 0) 0
  have hr : b₂ 0 = r • b₁ 0 := eq_repr_smul_basis_zero b₁ (b₂ 0)
  have hr0 : r ≠ 0 := by
    intro h
    apply b₂.ne_zero 0
    rw [hr, h, zero_smul]
  have hb₂ : b₂ = b₁.unitsSMul (Function.const (Fin 1) (Units.mk0 r hr0)) := by
    apply Basis.eq_of_apply_eq
    intro i
    fin_cases i
    simp [Basis.unitsSMul_apply, hr]
  have hpos : 0 < r := by
    rw [hb₂, Basis.orientation_unitsSMul, ← h₁, units_smul_eq_self_iff] at h₂
    simpa using h₂
  have hs : 0 < a + c * r := by
    rcases eq_or_lt_of_le hc with h | h
    · subst h
      simp only [add_zero] at hac
      simp [hac]
    · nlinarith [mul_pos h hpos]
  obtain ⟨b, hb, hbo⟩ := basis_orientation_smul b₁ hs
  refine ⟨b, ?_, hbo.trans h₁⟩
  rw [hb, hr, smul_smul, add_smul]

theorem basis_orientation_map (f : V ≃ₗ[ℝ] W) {o : Orientation ℝ V (Fin 1)} {w : V}
    (h : ∃ b : Basis (Fin 1) ℝ V, b 0 = w ∧ b.orientation = o) :
    ∃ b : Basis (Fin 1) ℝ W, b 0 = f w ∧ b.orientation = Orientation.map (Fin 1) f o := by
  obtain ⟨b, rfl, rfl⟩ := h
  exact ⟨b.map f, by simp, b.orientation_map f⟩

theorem ne_of_basis_orientation_neg {o : Orientation ℝ V (Fin 1)} {w w' : V}
    (hw : ∃ b : Basis (Fin 1) ℝ V, b 0 = w ∧ b.orientation = o)
    (hw' : ∃ b : Basis (Fin 1) ℝ V, b 0 = w' ∧ b.orientation = -o) : w ≠ w' := by
  rintro rfl
  obtain ⟨b, hb, rfl⟩ := hw
  obtain ⟨b', hb', ho⟩ := hw'
  have hbb : b' = b := Basis.eq_of_apply_eq fun i => by
    fin_cases i
    exact hb'.trans hb.symm
  rw [hbb] at ho
  exact Module.Ray.ne_neg_self b.orientation ho

end LinearAlgebra

section PositiveField

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem exists_positive_vectorField [T2Space M] [SigmaCompactSpace M]
    (hdim : finrank ℝ E = 1) (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin 1))
    (ho : DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E)
      (TangentSpace I) o) :
    ∃ v : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, v x⟩ : TangentBundle I M)) ∧
      ∀ x, ∃ b : Basis (Fin 1) ℝ (TangentSpace I x), b 0 = v x ∧ b.orientation = o x := by
  have hloc : ∀ x₀ : M, ∃ U ∈ 𝓝 x₀, ∃ sl : (x : M) → TangentSpace I x,
      ContMDiffOn I I.tangent ∞ (fun y => (⟨y, sl y⟩ : TangentBundle I M)) U ∧
      ∀ y ∈ U, ∃ b : Basis (Fin 1) ℝ (TangentSpace I y), b 0 = sl y ∧ b.orientation = o y := by
    intro x₀
    obtain ⟨t, ht, U, hU, hUt, p, hp⟩ := ho x₀
    obtain ⟨b, hb⟩ := exists_basis_orientation_eq hdim p
    refine ⟨U, hU, fun y => t.symmL ℝ y (b 0), ?_, ?_⟩
    · have hon : ContMDiffOn I I.tangent ∞
          (fun y => (⟨y, t.symmL ℝ y (b 0)⟩ : TangentBundle I M)) t.baseSet := by
        rw [t.contMDiffOn_section_baseSet_iff]
        refine (contMDiffOn_const (c := b 0)).congr fun y hy => ?_
        change (t ⟨y, t.symmL ℝ y (b 0)⟩).2 = b 0
        rw [t.symmL_apply (R := ℝ) hy, t.apply_mk_symm hy]
      exact hon.mono hUt
    · intro y hy
      let L := (t.continuousLinearEquivAt ℝ y (hUt hy)).toLinearEquiv
      obtain ⟨b', hb'0, hb'o⟩ := basis_orientation_map L.symm (o := p) (w := b 0) ⟨b, rfl, hb⟩
      refine ⟨b', ?_, ?_⟩
      · rw [hb'0]
        change (t.continuousLinearEquivAt ℝ y (hUt hy)).symm (b 0) = t.symmL ℝ y (b 0)
        rw [t.symm_continuousLinearEquivAt_eq (R := ℝ) (hUt hy)]
      · rw [hb'o, ← hp y hy, ← Orientation.map_symm]
        exact (Orientation.map (Fin 1) L).symm_apply_apply (o y)
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local I (n := ⊤) (F_fiber := E)
    (TangentSpace I : M → Type _)
    (fun x => {w : TangentSpace I x |
      ∃ b : Basis (Fin 1) ℝ (TangentSpace I x), b 0 = w ∧ b.orientation = o x})
    (fun x => convex_basis_orientation (o x)) hloc
  exact ⟨fun x => s x, s.contMDiff, hs⟩

end PositiveField

section Orientability

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Analysis.ODE in
theorem not_connectedSpace_tangentOrientationCover [T2Space M] [CompactSpace M]
    (hdim : finrank ℝ E = 1) :
    ¬ ConnectedSpace (tangentOrientationCover (M := M) hdim) := by
  intro hconn
  let := tangentOrientationChartedSpace (M := M) hdim
  have := tangentOrientation_isManifold (M := M) hdim
  have := tangentOrientationCover_t2Space (M := M) hdim
  have := tangentOrientationCover_compactSpace (M := M) hdim
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨v, hv, hvpos⟩ := exists_positive_vectorField (I := 𝓘(ℝ, E))
    (M := tangentOrientationCover (M := M) hdim) hdim (tangentOrientationCanonical hdim)
    (tangentOrientationCanonical_compatible hdim)
  let τ := tangentOrientationDeckDiffeomorph (M := M) hdim
  have hττ : ∀ z, τ (τ z) = z := tangentOrientationDeck_involutive hdim
  let D := fun z : tangentOrientationCover (M := M) hdim =>
    τ.mfderivToContinuousLinearEquiv (by decide) z
  let P := VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) τ v
  have hP : ∀ z, P z = (D z).symm (v (τ z)) := by
    intro z
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) τ z).inverse (v (τ z)) = _
    rw [← τ.mfderivToContinuousLinearEquiv_coe (by decide), ContinuousLinearMap.inverse_equiv]
    rfl
  let u := v - P
  have hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun z => (⟨z, u z⟩ : TangentBundle 𝓘(ℝ, E) (tangentOrientationCover (M := M) hdim))) :=
    hv.sub_section (hv.mpullback_vectorField τ.contMDiff
      (fun z => τ.isInvertible_mfderiv (by decide)) (by simp))
  have hchain : ∀ z (w : TangentSpace 𝓘(ℝ, E) z), D (τ z) (D z w) = w := by
    intro z w
    have hc := mfderiv_comp_apply (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E))
      (g := (τ : _ → _)) (f := (τ : _ → _)) (x := z)
      (τ.contMDiff.mdifferentiable (by decide) (τ z))
      (τ.contMDiff.mdifferentiable (by decide) z) w
    have heq : (τ : _ → _) ∘ τ = id := funext hττ
    rw [heq, mfderiv_id] at hc
    exact hc.symm
  have hanti : ∀ z, D z (u z) = -u (τ z) := by
    intro z
    have hPτ : P (τ z) = D z (v z) := by
      apply (D (τ z)).injective
      rw [hP (τ z), ContinuousLinearEquiv.apply_symm_apply, hchain z (v z)]
      exact congrArg (fun y => (v y : E)) (hττ z)
    change D z (v z - P z) = -(v (τ z) - P (τ z))
    rw [map_sub, hP z, ContinuousLinearEquiv.apply_symm_apply, hPτ]
    abel
  have hne : ∀ z, u z ≠ 0 := by
    intro z hz
    have hpos := hvpos z
    have hneg : ∃ b : Basis (Fin 1) ℝ (TangentSpace 𝓘(ℝ, E) z), b 0 = P z ∧
        b.orientation = -tangentOrientationCanonical hdim z := by
      obtain ⟨b, hb0, hbo⟩ := basis_orientation_map (D z).symm.toLinearEquiv (hvpos (τ z))
      refine ⟨b, hb0.trans (hP z).symm, hbo.trans ?_⟩
      have key : Orientation.map (Fin 1) (D z).toLinearEquiv (tangentOrientationCanonical hdim z) =
          -tangentOrientationCanonical hdim (τ z) :=
        tangentOrientationDeck_reverses_canonical hdim z
      rw [ContinuousLinearEquiv.toLinearEquiv_symm, ← Orientation.map_symm, Equiv.symm_apply_eq,
        Orientation.map_neg, key]
      exact (neg_neg (tangentOrientationCanonical hdim (τ z))).symm
    exact ne_of_basis_orientation_neg hpos hneg (sub_eq_zero.mp hz)
  have hu1 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun z => (⟨z, u z⟩ : TangentBundle 𝓘(ℝ, E) (tangentOrientationCover (M := M) hdim))) :=
    hu.of_le (by norm_num)
  have hc := exists_globalIntegralCurve_of_compactSupport u hu (isClosed_tsupport u).isCompact
  have hsmooth := contMDiff_curveAt u hu hc
  let φ : _root_.Flow ℝ (tangentOrientationCover (M := M) hdim) :=
    { toFun := fun t x => curveAt u hc x t
      cont' := hsmooth.continuous
      map_zero' := curveAt_zero u hc
      map_add' := fun s t x => by simpa only [add_comm] using curveAt_add u hu1 hc x t s }
  have hopen : ∀ x, IsOpenMap (fun t : ℝ => φ t x) := by
    intro x
    have hld : IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => φ t x) := by
      apply isLocalDiffeomorph_of_injective_mfderiv (fun t : ℝ => φ t x)
        (hsmooth.comp (contMDiff_id.prodMk contMDiff_const))
      · intro t
        change Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => curveAt u hc x s) t)
        rw [(curveAt_integralCurve u hc x t).mfderiv]
        change Function.Injective (fun a : ℝ => a • u (φ t x))
        exact smul_left_injective ℝ (hne (φ t x))
      · simpa using hdim.symm
    exact hld.isOpenMap
  have hconj : ∀ z t, τ (curveAt u hc z (t * -1)) = curveAt u hc (τ z) t := by
    intro z
    have hγ := (curveAt_integralCurve u hc z).comp_mul (-1)
    have hσ : IsMIntegralCurve (fun t => τ (curveAt u hc z (t * -1))) u := by
      intro t
      have h2 := ((τ.contMDiff.mdifferentiable (by decide))
        (curveAt u hc z (t * -1))).hasMFDerivAt.comp t (hγ t)
      refine h2.congr_mfderiv ?_
      refine ContinuousLinearMap.ext_ring ?_
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) τ (curveAt u hc z (t * -1))
        ((1 : ℝ) • ((-1 : ℝ) • u (curveAt u hc z (t * -1)))) =
        (1 : ℝ) • u (τ (curveAt u hc z (t * -1)))
      rw [← τ.mfderivToContinuousLinearEquiv_coe (by decide)]
      change D _ _ = _
      rw [one_smul, one_smul, map_smul, hanti, smul_neg, neg_smul, one_smul, neg_neg]
    have heq := integralCurve_eq_of_agree (t₀ := 0) u hu1 hσ (curveAt_integralCurve u hc (τ z))
      (by simp [curveAt_zero])
    exact fun t => congrFun heq t
  obtain ⟨z₀⟩ := hconn.toNonempty
  have hz₀ : τ z₀ ∈ φ.orbit z₀ := by
    rw [DifferentialGeometry.Topology.Flow.orbit_eq_univ_of_isOpenMap φ hopen z₀]
    exact mem_univ _
  obtain ⟨s, hs⟩ := φ.mem_orbit_iff.mp hz₀
  have hfix : τ (curveAt u hc z₀ (s / 2)) = curveAt u hc z₀ (s / 2) := by
    have h1 := hconj z₀ (-(s / 2))
    rw [show -(s / 2) * -1 = s / 2 by ring] at h1
    change curveAt u hc z₀ s = τ z₀ at hs
    rw [h1, ← hs, ← curveAt_add u hu1 hc z₀ s (-(s / 2))]
    congr 1
    ring
  exact tangentOrientationDeck_ne_self hdim _ hfix

open DifferentialGeometry.Topology.Manifold in
theorem exists_compatibleOrientation_of_finrank_eq_one [T2Space M] [CompactSpace M]
    [ConnectedSpace M] (hdim : finrank ℝ E = 1) :
    ∃ o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin 1),
      DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E)
        (TangentSpace 𝓘(ℝ, E)) o :=
  exists_compatibleOrientation_of_orientationCover_not_connected hdim
    (not_connectedSpace_tangentOrientationCover hdim)

theorem exists_nonvanishing_vectorField_of_finrank_eq_one [T2Space M] [CompactSpace M]
    [ConnectedSpace M] (hdim : finrank ℝ E = 1) :
    ∃ v : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      ∀ x, v x ≠ 0 := by
  obtain ⟨o, ho⟩ := exists_compatibleOrientation_of_finrank_eq_one (M := M) hdim
  obtain ⟨v, hv, hpos⟩ := exists_positive_vectorField hdim o ho
  refine ⟨v, hv, fun x => ?_⟩
  obtain ⟨b, hb, -⟩ := hpos x
  rw [← hb]
  exact b.ne_zero 0

theorem nonempty_addCircle_diffeomorph_of_finrank_eq_one [T2Space M] [CompactSpace M]
    [ConnectedSpace M] (hdim : finrank ℝ E = 1) :
    Nonempty (AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, E)⟯ M) := by
  obtain ⟨v, hv, hne⟩ := exists_nonvanishing_vectorField_of_finrank_eq_one (M := M) hdim
  exact DifferentialGeometry.Topology.Flow.exists_addCircle_diffeomorph_of_nonvanishing_vectorField
    hdim v hv hne

end Orientability

theorem nonempty_circle_diffeomorph_of_finrank_eq_one
    (E : Type uE) (H : Type uH) (F : Type uM) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace F] [ChartedSpace H F]
    (J : ModelWithCorners ℝ E H) [J.Boundaryless] [IsManifold J ∞ F] [T2Space F]
    [CompactSpace F] [ConnectedSpace F] (hdim : Module.finrank ℝ E = 1) :
    Nonempty (Circle ≃ₘ⟮𝓡 1, J⟯ F) := by
  let : ChartedSpace E F := ChartedSpace.transHomeomorph J.toHomeomorph
  have : IsManifold 𝓘(ℝ, E) ∞ F :=
    ChartedSpace.isManifold_transHomeomorph (I := J) J.toHomeomorph (fun x => rfl)
  obtain ⟨e⟩ := nonempty_addCircle_diffeomorph_of_finrank_eq_one (M := F) hdim
  exact ⟨(AddCircle.diffeomorphCircle.symm.trans e).trans
    (ChartedSpace.transHomeomorphDiffeomorph J 𝓘(ℝ, E) J.toHomeomorph (fun x => rfl) ∞).symm⟩

end DifferentialGeometry.Topology.Manifold.OneManifold
