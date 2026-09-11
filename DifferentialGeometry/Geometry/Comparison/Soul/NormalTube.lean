import DifferentialGeometry.Geometry.Comparison.Soul.NormalTubeInjectivity
import DifferentialGeometry.Geometry.Comparison.Soul.NearestPointAngles

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section LocalInverseGluing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]

private theorem isOpen_localDiffeomorphLocus (f : M → N) :
    IsOpen {x | IsLocalDiffeomorphAt I J ∞ f x} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨Φ, hx, hΦ⟩
  exact Filter.mem_of_superset (Φ.open_source.mem_nhds hx)
    (fun y hy => ⟨Φ, hy, hΦ⟩)

private def partialDiffeomorphOfBijOn [Nonempty M]
    {f : M → N} {U : Set M} {V : Set N}
    (hU : IsOpen U) (hV : IsOpen V) (hbij : BijOn f U V)
    (hf : ContMDiffOn I J ∞ f U)
    (hloc : ∀ x ∈ U, IsLocalDiffeomorphAt I J ∞ f x) :
    PartialDiffeomorph I J M N ∞ := by
  classical
  let e := hbij.toPartialEquiv f U V
  have hinverse : ContMDiffOn J I ∞ (e.symm : N → M) V := by
    intro y hy
    let x := e.symm y
    have hx : x ∈ U := e.map_target hy
    have hfx : f x = y := e.right_inv hy
    have hl := hloc x hx
    let ψ := hl.localInverse
    have hψy : ContMDiffAt J I ∞ (ψ : N → M) y := by
      rw [← hfx]
      exact hl.localInverse_contMDiffAt
    have hψyx : ψ y = x := by
      rw [← hfx]
      exact hl.localInverse_left_inv hl.localInverse_mem_target
    have hyψ : y ∈ ψ.source := by
      rw [← hfx]
      exact hl.localInverse_mem_source
    have hψU : ∀ᶠ z in 𝓝 y, ψ z ∈ U :=
      hψy.continuousAt (by simpa only [hψyx] using hU.mem_nhds hx)
    have hagree : (e.symm : N → M) =ᶠ[𝓝 y] (ψ : N → M) := by
      filter_upwards [hV.mem_nhds hy, ψ.open_source.mem_nhds hyψ, hψU] with z hz hzψ hzU
      apply hbij.injOn (e.map_target hz) hzU
      calc
        f (e.symm z) = z := by
          change e (e.symm z) = z
          exact e.right_inv hz
        _ = f (ψ z) := (hl.localInverse_right_inv hzψ).symm
    exact (hψy.congr_of_eventuallyEq hagree).contMDiffWithinAt
  exact
    { toPartialEquiv := e
      open_source := hU
      open_target := hV
      contMDiffOn_toFun := hf
      contMDiffOn_invFun := hinverse }

end LocalInverseGluing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
  {S : Set M}

local notation "FB" => (Fin (maxSliceDim I S) → ℝ)
local notation "FN" => (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
local notation "IN" => ModelWithCorners.prod
  (modelWithCornersSelf ℝ (Fin (maxSliceDim I S) → ℝ))
  (modelWithCornersSelf ℝ (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ))
local notation "NB" => TotalSpace FN (normalBundleFiber (I := I) g S)

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem normalExp_infDist_le (z : NB) :
    Metric.infDist (normalExp (I := I) g hEnorm S z) S ≤
      Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) := by
  exact (Metric.infDist_le_dist_of_mem z.proj.2).trans
    ((dist_comm _ _).le.trans (dist_normalExp_le_length g hEnorm z))

private theorem exists_normal_exp_length_eq_infDist
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (hSne : S.Nonempty) (hScomp : IsCompact S) (hconv : IsTotallyConvex (I := I) g S)
    (hB : relBoundary I S = ∅) (q : M) :
    ∃ z : NB, normalExp (I := I) g hEnorm S z = q ∧
      Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) = Metric.infDist q S := by
  obtain ⟨p, hp, v, hexp, hv, hn⟩ :=
    exists_minimizing_normal_exp g hEnorm hsec hSne hScomp hconv hB q
  let z : NB := ⟨⟨p, hp⟩, ⟨v, (mem_normalSpace_iff g S p v).mpr hn⟩⟩
  refine ⟨z, hexp, ?_⟩
  change Real.sqrt (g.inner p v v) = Metric.infDist q S
  rw [hv, Real.sqrt_sq Metric.infDist_nonneg]

theorem exists_normal_tube
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (hSne : S.Nonempty) (hScomp : IsCompact S) (hconv : IsTotallyConvex (I := I) g S)
    (hB : relBoundary I S = ∅) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    ∃ ε > 0, ∃ Φ : PartialDiffeomorph IN I NB M ∞,
      Φ.source = {z | Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) < ε} ∧
      Φ.target = {q | Metric.infDist q S < ε} ∧
      (Φ : NB → M) = normalExp (I := I) g hEnorm S ∧
      (∀ p : S, (⟨p, 0⟩ : NB) ∈ Φ.source ∧ Φ ⟨p, 0⟩ = p.1) ∧
      ∀ z ∈ Φ.source,
        Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) = Metric.infDist (Φ z) S := by
  classical
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  let _ : Nonempty NB := ⟨⟨⟨hSne.choose, hSne.choose_spec⟩, 0⟩⟩
  let f : NB → M := normalExp (I := I) g hEnorm S
  let L : NB → ℝ := fun z => Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1)
  have hf : ContMDiff IN I ∞ f := normalExp_contMDiff g hEnorm hconv hB
  have hL : Continuous L := normalLength_continuous g hEnorm hconv hB
  let U : Set NB := {z | IsLocalDiffeomorphAt IN I ∞ f z}
  have hU : IsOpen U := isOpen_localDiffeomorphLocus f
  have hzero : ∀ p : S, (⟨p, 0⟩ : NB) ∈ U :=
    fun p => normalExp_isLocalDiffeomorphAt_zero g hEnorm hconv hB p
  obtain ⟨r₁, hr₁, hlocal⟩ :=
    exists_normal_radius_subset_of_isOpen g hEnorm hScomp hconv hB U hU hzero
  obtain ⟨r₂, hr₂, hinj⟩ := exists_normalExp_injOn_disk g hEnorm hScomp hconv hB
  let ε := min r₁ r₂
  have hε : 0 < ε := lt_min hr₁ hr₂
  let D : Set NB := {z | L z < ε}
  let V : Set M := {q | Metric.infDist q S < ε}
  have hD : IsOpen D := isOpen_lt hL continuous_const
  have hV : IsOpen V := isOpen_lt (Metric.continuous_infDist_pt S) continuous_const
  have hDlocal : ∀ z ∈ D, IsLocalDiffeomorphAt IN I ∞ f z := by
    intro z hz
    exact hlocal z (lt_of_lt_of_le hz (min_le_left r₁ r₂))
  have hDinj : InjOn f D := hinj.mono (fun z hz =>
    lt_of_lt_of_le hz (min_le_right r₁ r₂))
  have hmaps : MapsTo f D V := by
    intro z hz
    exact lt_of_le_of_lt (normalExp_infDist_le g hEnorm z) hz
  have hsurj : SurjOn f D V := by
    intro q hq
    obtain ⟨z, hz, hlen⟩ :=
      exists_normal_exp_length_eq_infDist g hEnorm hsec hSne hScomp hconv hB q
    refine ⟨z, ?_, hz⟩
    change L z < ε
    exact hlen.trans_lt hq
  have hlength : ∀ z ∈ D, L z = Metric.infDist (f z) S := by
    intro z hz
    obtain ⟨w, hwf, hwlen⟩ :=
      exists_normal_exp_length_eq_infDist g hEnorm hsec hSne hScomp hconv hB (f z)
    have hwD : w ∈ D := hwlen.trans_lt (hmaps hz)
    have hzw : z = w := hDinj hz hwD hwf.symm
    exact (congrArg L hzw).trans hwlen
  have hbij : BijOn f D V := ⟨hmaps, hDinj, hsurj⟩
  let Φ : PartialDiffeomorph IN I NB M ∞ :=
    partialDiffeomorphOfBijOn hD hV hbij hf.contMDiffOn hDlocal
  refine ⟨ε, hε, Φ, rfl, rfl, rfl, ?_, ?_⟩
  · intro p
    constructor
    · change Real.sqrt (g.inner p.1 (0 : TangentSpace I p.1) 0) < ε
      simpa only [map_zero, Real.sqrt_zero] using hε
    · exact normalExp_zero g hEnorm p
  · exact hlength

end DifferentialGeometry.Geometry.Topology

end
