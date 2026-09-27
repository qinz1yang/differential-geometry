import DifferentialGeometry.Geometry.Curvature.NeckChartLeastRicci
import DifferentialGeometry.Geometry.Curvature.LeastRicciRestriction
import DifferentialGeometry.Geometry.VectorField.OpenExtension
import DifferentialGeometry.Topology.Manifold.OpenFunctionExtension

noncomputable section
open Set Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.VectorField
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Curvature

theorem exists_ambient_least_ricci_field_close_to_gradient_from_neck_chart
    {E F H M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M]
    (O : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (V : TopologicalSpace.Opens M) (g : SmoothRiemannianMetric J M)
    (Φ : O ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), J⟯ V)
    (Q : ℝ) (hQ : 0 < Q) {U : Set O} (hU : IsOpen U)
    (ε : ℝ) (hε : ε < 1 / 200000)
    (hsmall : ∀ x ∈ U, ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k (Diffeomorph.pullbackMetricCross (scaleMetric Q hQ (g.restrictOpen V)) Φ)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen O)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen O) x ≤ ε) :
    let uV : V → ℝ := fun y ↦ (Real.sqrt Q)⁻¹ * (Φ.symm y : Metric.sphere (0 : E) 1 × ℝ).2
    let u : M → ℝ := Subtype.val.extend uV (fun _ ↦ 0)
    ∃ (ν : M → ℝ) (Y : ∀ y : M, TangentSpace J y),
      ContMDiffOn J 𝓘(ℝ) ∞ u V ∧
      ContMDiffOn J 𝓘(ℝ) ∞ ν (Subtype.val '' (Φ '' U)) ∧
      ContMDiffOn J J.tangent ∞ (fun y ↦ (⟨y, Y y⟩ : TangentBundle J M)) (Subtype.val '' (Φ '' U)) ∧
      ∀ y ∈ Subtype.val '' (Φ '' U), g.inner y (Y y) (Y y) = 1 ∧
        ricciSharp g y (Y y) = ν y • Y y ∧
        (∀ z : TangentSpace J y, g.inner y z z = 1 → ν y ≤ ricciTensor g y z z) ∧
        |ν y| ≤ 5772 * Q * ε ∧
        Module.End.eigenspace (ricciSharp g y).toLinearMap (ν y) = Submodule.span ℝ {Y y} ∧
        0 < mvfderiv J u y (Y y) ∧ |mvfderiv J u y (Y y) - 1| ≤ 92354 * ε ∧
        Real.sqrt (g.inner y (Y y - gradFun g u y) (Y y - gradFun g u y)) ≤ 184712 * ε := by
  let : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [show Module.finrank ℝ E = 2 + 1 from Fact.out]
    norm_num)
  let : SigmaCompactSpace O := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ((𝓡 2).prod 𝓘(ℝ)) O.isOpen)
  have hrange : range (Φ : O → V) = univ := Φ.surjective.range_eq
  let : SigmaCompactSpace V := isSigmaCompact_univ_iff.mp
    (hrange ▸ isSigmaCompact_range Φ.continuous)
  let uV : V → ℝ := fun y ↦ (Real.sqrt Q)⁻¹ * (Φ.symm y : Metric.sphere (0 : E) 1 × ℝ).2
  have huV : ContMDiff J 𝓘(ℝ) ∞ uV :=
    contMDiff_const.mul ((contMDiff_snd.comp contMDiff_subtype_val).comp Φ.symm.contMDiff)
  obtain ⟨ν₀, Y₀, hν₀, hY₀, hprop⟩ :=
    exists_smooth_least_ricci_field_close_to_gradient_from_neck_chart
      O (g.restrictOpen V) Φ Q hQ hU ε hε hsmall
  let ν : M → ℝ := Subtype.val.extend ν₀ (fun _ ↦ 0)
  let Y := extendOpenTangentField V Y₀
  have hA : IsOpen (Φ '' U) := Φ.toHomeomorph.isOpenMap _ hU
  have hu : ContMDiffOn J 𝓘(ℝ) ∞ (Subtype.val.extend uV (fun _ : M ↦ (0 : ℝ))) V := by
    have h := contMDiffOn_extend_from_open V uV (fun _ : M ↦ (0 : ℝ)) isOpen_univ huV.contMDiffOn
    have hi : (Subtype.val : V → M) '' (univ : Set V) = (V : Set M) := by
      ext x
      simp
    rwa [hi] at h
  refine ⟨ν, Y, hu, contMDiffOn_extend_from_open V ν₀ _ hA hν₀,
    contMDiffOn_extendOpenTangentField V Y₀ hA hY₀, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hνeq : ν (x : M) = ν₀ x := Subtype.val_injective.extend_apply _ _ x
  have hYeq : Y (x : M) = mfderiv J J (Subtype.val : V → M) x (Y₀ x) :=
    extendOpenTangentField_apply V Y₀ x
  rw [hνeq, hYeq]
  obtain ⟨hunit, heig, hmin, hbound, hsimple, hpos, hderiv, hgrad⟩ := hprop x hx
  obtain ⟨hn, he, hm, hs⟩ :=
    least_ricci_eigenpair_restrictOpen g V x (ν₀ x) (Y₀ x) hunit heig hmin hsimple
  refine ⟨hn, he, hm, hbound, hs, ?_, ?_, ?_⟩
  · rwa [mvfderiv_extend_from_open V uV _ huV]
  · rwa [mvfderiv_extend_from_open V uV _ huV]
  · have hgrad_eq : gradFun g (Subtype.val.extend uV (fun _ : M ↦ 0)) (x : M) =
        gradFun (g.restrictOpen V) uV x := by
      apply metricFlatLinear_injective g (x : M)
      ext v
      change g.inner (x : M) (gradFun g (Subtype.val.extend uV (fun _ : M ↦ 0)) (x : M)) v =
        (g.restrictOpen V).inner x (gradFun (g.restrictOpen V) uV x) v
      erw [inner_gradFun, inner_gradFun]
      have h := mvfderiv_extend_from_open V uV (fun _ : M ↦ 0) huV x v
      change mfderiv J 𝓘(ℝ) (Subtype.val.extend uV (fun _ : M ↦ 0)) (x : M)
        (mfderiv J J (Subtype.val : V → M) x v) = mfderiv J 𝓘(ℝ) uV x v at h
      erw [mfderiv_subtype_val_apply] at h
      exact h
    rw [hgrad_eq, mfderiv_subtype_val_apply]
    exact hgrad

theorem exists_ambient_least_ricci_field_from_neck_chart
    {E F H M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M]
    (O : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (V : TopologicalSpace.Opens M) (g : SmoothRiemannianMetric J M)
    (Φ : O ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), J⟯ V)
    (Q : ℝ) (hQ : 0 < Q) {U : Set O} (hU : IsOpen U)
    (ε : ℝ) (hε : ε < 1 / 200000)
    (hsmall : ∀ x ∈ U, ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k (Diffeomorph.pullbackMetricCross (scaleMetric Q hQ (g.restrictOpen V)) Φ)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen O)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen O) x ≤ ε) :
    let uV : V → ℝ := fun y ↦ (Real.sqrt Q)⁻¹ * (Φ.symm y : Metric.sphere (0 : E) 1 × ℝ).2
    let u : M → ℝ := Subtype.val.extend uV (fun _ ↦ 0)
    ∃ (ν : M → ℝ) (Y : ∀ y : M, TangentSpace J y),
      ContMDiffOn J 𝓘(ℝ) ∞ u V ∧
      ContMDiffOn J 𝓘(ℝ) ∞ ν (Subtype.val '' (Φ '' U)) ∧
      ContMDiffOn J J.tangent ∞ (fun y ↦ (⟨y, Y y⟩ : TangentBundle J M)) (Subtype.val '' (Φ '' U)) ∧
      ∀ y ∈ Subtype.val '' (Φ '' U), g.inner y (Y y) (Y y) = 1 ∧
        ricciSharp g y (Y y) = ν y • Y y ∧
        (∀ z : TangentSpace J y, g.inner y z z = 1 → ν y ≤ ricciTensor g y z z) ∧
        |ν y| ≤ 5772 * Q * ε ∧
        Module.End.eigenspace (ricciSharp g y).toLinearMap (ν y) = Submodule.span ℝ {Y y} ∧
        0 < mvfderiv J u y (Y y) ∧ |mvfderiv J u y (Y y) - 1| ≤ 92354 * ε := by
  obtain ⟨ν, Y, hu, hν, hY, hprop⟩ :=
    exists_ambient_least_ricci_field_close_to_gradient_from_neck_chart
      O V g Φ Q hQ hU ε hε hsmall
  refine ⟨ν, Y, hu, hν, hY, ?_⟩
  intro y hy
  obtain ⟨hn, he, hm, hb, hs, hp, hd, _⟩ := hprop y hy
  exact ⟨hn, he, hm, hb, hs, hp, hd⟩

end DifferentialGeometry.Geometry.Curvature
