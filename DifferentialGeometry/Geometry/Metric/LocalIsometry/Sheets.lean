import DifferentialGeometry.Geometry.Metric.LocalIsometry.PathLifting
import Mathlib.Analysis.Convex.Star
import Mathlib.Topology.Homotopy.Lifting

noncomputable section

open Bundle Manifold Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold J ∞ N]
  [T2Space M] [SigmaCompactSpace M] [T2Space N]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_openEmbedding_section_of_complete_of_starConvex
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f)
    (hg : RiemannianMetricComplete (I := I) g)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    (φ : PartialDiffeomorph 𝓘(ℝ, F) J F N ∞)
    (z₀ : F) (hz₀ : z₀ ∈ φ.source) (hstar : StarConvex ℝ z₀ φ.source)
    (x : M) (hx : f x = φ z₀) :
    ∃ σ : C(φ.target, M), σ ⟨φ z₀, φ.map_source hz₀⟩ = x ∧
      (∀ y : φ.target, f (σ y) = (y : N)) ∧ Topology.IsOpenEmbedding σ := by
  classical
  let γ (y : φ.target) (t : ℝ) : N := φ ((1 - t) • z₀ + t • φ.symm y)
  have hmem (y : φ.target) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (1 - t) • z₀ + t • φ.symm y ∈ φ.source :=
    hstar (φ.map_target y.property) (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel _ _)
  have hγ (y : φ.target) : ContMDiffOn 𝓘(ℝ) J 1 (γ y) (Icc (0 : ℝ) 1) := by
    have hcoords : ContMDiff 𝓘(ℝ) 𝓘(ℝ, F) 1
        (fun t : ℝ => (1 - t) • z₀ + t • φ.symm y) :=
      ((contMDiff_const.sub contMDiff_id).smul contMDiff_const).add
        (contMDiff_id.smul contMDiff_const)
    exact (φ.contMDiffOn_toFun.of_le (by simp)).comp hcoords.contMDiffOn (hmem y)
  have hγ0 (y : φ.target) : γ y 0 = φ z₀ := by simp [γ]
  have hγ1 (y : φ.target) : γ y 1 = y := by
    simp only [γ, sub_self, zero_smul, one_smul, zero_add]
    exact φ.right_inv y.property
  have hcoords : Continuous (fun y : φ.target => φ.symm (y : N)) :=
    continuousOn_iff_continuous_domRestrict.mp φ.contMDiffOn_invFun.continuousOn
  have htime : Continuous (fun p : unitInterval × φ.target => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hradial : Continuous (fun p : unitInterval × φ.target =>
      (1 - (p.1 : ℝ)) • z₀ + (p.1 : ℝ) • φ.symm (p.2 : N)) :=
    ((continuous_const.sub htime).smul continuous_const).add (htime.smul (hcoords.comp continuous_snd))
  let Γ : C(unitInterval × φ.target, N) :=
    ⟨fun p => γ p.2 p.1,
      φ.contMDiffOn_toFun.continuousOn.comp_continuous hradial (fun p => hmem p.2 p.1 p.1.property)⟩
  have hex (y : φ.target) : ∃ η : ℝ → M,
      ContMDiffOn 𝓘(ℝ) I 1 η (Icc (0 : ℝ) 1) ∧ η 0 = x ∧
      EqOn (f ∘ η) (γ y) (Icc (0 : ℝ) 1) ∧
      ∀ ζ : ℝ → M, ContinuousOn ζ (Icc (0 : ℝ) 1) → ζ 0 = x →
        EqOn (f ∘ ζ) (γ y) (Icc (0 : ℝ) 1) → EqOn ζ η (Icc (0 : ℝ) 1) :=
    exists_contMDiffOn_lift_of_complete g h hf hg hmetric zero_le_one (hγ y) x
      (hx.trans (hγ0 y).symm)
  choose η hη hη0 hηf hηuniq using hex
  let Λ : unitInterval × φ.target → M := fun p => η p.2 p.1
  have hΛf : f ∘ Λ = Γ := by
    funext p
    exact hηf p.2 p.1.property
  have hΛ0 : Continuous (fun y : φ.target => Λ (0, y)) := by
    have heq : (fun y : φ.target => Λ (0, y)) = fun _ => x := funext hη0
    rw [heq]
    exact continuous_const
  have hΛpath (y : φ.target) : Continuous (fun t : unitInterval => Λ (t, y)) :=
    (hη y).continuousOn.domRestrict
  have hΛ : Continuous Λ :=
    hf.isLocalHomeomorph.continuous_lift (T2Space.isSeparatedMap f) Γ hΛf hΛ0 hΛpath
  let σ : C(φ.target, M) := ⟨fun y => Λ (1, y), hΛ.comp (continuous_const.prodMk continuous_id)⟩
  have hσf (y : φ.target) : f (σ y) = y :=
    (hηf y (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)).trans (hγ1 y)
  have hσ0 : σ ⟨φ z₀, φ.map_source hz₀⟩ = x := by
    let y₀ : φ.target := ⟨φ z₀, φ.map_source hz₀⟩
    have hconst : ∀ t : ℝ, γ y₀ t = φ z₀ := by
      intro t
      change φ ((1 - t) • z₀ + t • φ.symm (φ z₀)) = φ z₀
      have hleft : φ.symm.toPartialEquiv (φ.toPartialEquiv z₀) = z₀ := φ.left_inv hz₀
      rw [hleft, ← add_smul, sub_add_cancel, one_smul]
    have heq := hηuniq y₀ (fun _ => x) continuousOn_const rfl
      (fun t _ => hx.trans (hconst t).symm)
    exact (heq (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)).symm
  refine ⟨σ, hσ0, hσf, ?_⟩
  apply hf.isLocalHomeomorph.isOpenEmbedding_of_comp ?_ σ.continuous
  have hcomp : f ∘ σ = (Subtype.val : φ.target → N) := funext hσf
  rw [hcomp]
  exact φ.open_target.isOpenEmbedding_subtypeVal

end DifferentialGeometry.Geometry.Riemannian
