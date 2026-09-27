import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Curvature.DiskSectionalDensity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskMetricVariation
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M]

variable {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {t : ℝ} {U : ℂ → M} {z : ℂ}

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem diskMapMetricVariationDensity_eq_neg_ricciTrace_of_hasDerivAt
    {Ric : M → E → E → ℝ}
    (h : ∀ X Y : E, HasDerivAt (fun r : ℝ => (G r).inner (U z) X Y)
      (-2 * Ric (U z) X Y) t) :
    diskMapMetricVariationDensity G t U z =
      -(Ric (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) +
        Ric (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)) := by
  have h1 := (h (diskMapPartial U z 1) (diskMapPartial U z 1)).deriv
  have h2 := (h (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)).deriv
  rw [diskMapMetricVariationDensity, h1, h2]
  ring

namespace Curvature

private theorem ricciTensor_smul_smul (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M)
    (s : ℝ) (X Y : TangentSpace 𝓘(ℝ, E) x) :
    ricciTensor (I := 𝓘(ℝ, E)) g x (s • X) (s • Y) =
      s * s * ricciTensor (I := 𝓘(ℝ, E)) g x X Y := by
  rw [map_smul, smul_eq_mul, map_smul, smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem inner_smul_smul (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M)
    (s : ℝ) (X Y : TangentSpace 𝓘(ℝ, E) x) :
    g.inner x (s • X) (s • Y) = s * s * g.inner x X Y := by
  rw [map_smul, smul_eq_mul, map_smul, smul_apply, smul_eq_mul]
  ring

omit [T2Space M] in
private theorem exists_orthonormalBasis_fin_three_of_orthonormal_pair
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (v w : TangentSpace 𝓘(ℝ, E) x)
    (hv : g.inner x v v = 1) (hw : g.inner x w w = 1) (hvw : g.inner x v w = 0) :
    ∃ B : Module.Basis (Fin 3) ℝ (TangentSpace 𝓘(ℝ, E) x),
      B 0 = v ∧ B 1 = w ∧
        ∀ i j : Fin 3, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 := by
  let D := (Tensor0SBundle.tangentMetricData (I := 𝓘(ℝ, E)) g x).metric
  let _ : InnerProductSpace.Core ℝ (TangentSpace 𝓘(ℝ, E) x) := D.toCore
  let _ : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace 𝓘(ℝ, E) x) _ _ _ D.toCore
  let _ : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    @InnerProductSpace.ofCore ℝ (TangentSpace 𝓘(ℝ, E) x) _ _ _ D.toCore.toCore
  have hg : ∀ a b : TangentSpace 𝓘(ℝ, E) x, g.inner x a b = Inner.inner ℝ a b := by
    intro a b
    rw [← Tensor0SBundle.TangentMetricData.inner_eq
      (Tensor0SBundle.tangentMetricData (I := 𝓘(ℝ, E)) g x) a b]
    change D.inner a b = Inner.inner ℝ a b
    exact (Tensor0SBundle.MetricFiberData.toCore_inner D a b).symm
  have hcard : Module.finrank ℝ (TangentSpace 𝓘(ℝ, E) x) = Fintype.card (Fin 3) := by
    rw [Fintype.card_fin]
    exact hdim
  let vv : Fin 3 → TangentSpace 𝓘(ℝ, E) x := ![v, w, 0]
  let s : Set (Fin 3) := {0, 1}
  have hv0 : vv 0 = v := rfl
  have hv1 : vv 1 = w := rfl
  have hvON : Orthonormal ℝ (s.domRestrict vv) := by
    refine ⟨?_, ?_⟩
    · intro ⟨i, hi⟩
      simp only [Set.domRestrict_apply]
      rcases hi with h | h
      · subst h
        rw [hv0, norm_eq_sqrt_real_inner, ← hg v v, hv, Real.sqrt_one]
      · subst h
        rw [hv1, norm_eq_sqrt_real_inner, ← hg w w, hw, Real.sqrt_one]
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only [Set.domRestrict_apply]
      rcases hi with h | h <;> rcases hj with h' | h' <;> subst h <;> subst h'
      · exact absurd rfl hij
      · rw [hv0, hv1, ← hg v w, hvw]
      · rw [hv0, hv1, ← hg w v, g.symm x w v, hvw]
      · exact absurd rfl hij
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ) hcard hvON
  refine ⟨b.toBasis, ?_, ?_, ?_⟩
  · have h := hb 0 (by decide)
    rw [hv0] at h
    rw [← h]
    rfl
  · have h := hb 1 (by decide)
    rw [hv1] at h
    rw [← h]
    rfl
  · intro i j
    have h1 : b.toBasis i = b i := rfl
    have h2 : b.toBasis j = b j := rfl
    rw [h1, h2, hg (b i) (b j), b.inner_eq_ite i j]

theorem ricciTensor_add_eq_sectionalCurvature_add_half_metricScalarAt_of_orthonormalBasis
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace 𝓘(ℝ, E) x))
    (hON : ∀ i j : Fin 3, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0) :
    ricciTensor (I := 𝓘(ℝ, E)) g x (basis 0) (basis 0) +
        ricciTensor (I := 𝓘(ℝ, E)) g x (basis 1) (basis 1) =
      sectionalCurvature (I := 𝓘(ℝ, E)) g x (basis 0) (basis 1) +
        metricScalarAt (I := 𝓘(ℝ, E)) g x / 2 := by
  let Rm : TangentSpace 𝓘(ℝ, E) x → TangentSpace 𝓘(ℝ, E) x →
      TangentSpace 𝓘(ℝ, E) x → TangentSpace 𝓘(ℝ, E) x → ℝ :=
    fun X Y Z W => metricRm04StandardAt (I := 𝓘(ℝ, E)) (M := M) g x X Y Z W
  have hinput : ∀ X Y Z W : TangentSpace 𝓘(ℝ, E) x, Rm Y X Z W = -Rm X Y Z W := by
    intro X Y Z W
    simpa [Rm, metricRm04StandardAt_apply, metricRm04_apply] using
      (rm04InputSkewAt_of_leviCivita_realizes (I := 𝓘(ℝ, E)) g
        (metricRm04 (I := 𝓘(ℝ, E)) (M := M) g)
        (metricCurvatureSections (I := 𝓘(ℝ, E)) (M := M) g).rm04Realizes X Y Z W)
  have hpair : ∀ X Y Z W : TangentSpace 𝓘(ℝ, E) x, Rm X Y Z W = Rm Z W X Y := by
    intro X Y Z W
    simpa [Rm, metricRm04StandardAt_apply, metricRm04_apply] using
      (rm04PairSymmAt_of_leviCivita_realizes (I := 𝓘(ℝ, E)) g
        (metricRm04 (I := 𝓘(ℝ, E)) (M := M) g)
        (metricCurvatureSections (I := 𝓘(ℝ, E)) (M := M) g).rm04Realizes X Y Z W)
  have hzero (i : Fin 3) : Rm (basis i) (basis i) (basis i) (basis i) = 0 := by
    have h := hinput (basis i) (basis i) (basis i) (basis i)
    linarith
  have hsec (i j : Fin 3) (hij : i ≠ j) :
      Rm (basis i) (basis j) (basis j) (basis i) =
        sectionalCurvature (I := 𝓘(ℝ, E)) g x (basis i) (basis j) :=
    (sectionalCurvature_eq_metricRm04StandardAt_of_unit_orthogonal (I := 𝓘(ℝ, E)) g x
      (basis i) (basis j) (by simpa using hON i i) (by simpa using hON j j)
      (by simpa [hij] using hON i j)).symm
  have hscal : metricScalarAt (I := 𝓘(ℝ, E)) g x =
      ∑ i : Fin 3, ricciTensor (I := 𝓘(ℝ, E)) g x (basis i) (basis i) :=
    DifferentialGeometry.Geometry.Curvature.metricScalarAt_eq_orthonormal_trace
      (I := 𝓘(ℝ, E)) g x basis hON
  have hdiag (i : Fin 3) : ricciTensor (I := 𝓘(ℝ, E)) g x (basis i) (basis i) =
      ∑ a : Fin 3, Rm (basis a) (basis i) (basis i) (basis a) := by
    have h := ricci_diag_eq_sum_rm04_diag_of_orthonormal (I := 𝓘(ℝ, E)) (M := M)
      (Idx := Fin 3) g basis
      (metricRicci (I := 𝓘(ℝ, E)) (M := M) g)
      (metricRm13 (I := 𝓘(ℝ, E)) (M := M) g)
      (metricRm04 (I := 𝓘(ℝ, E)) (M := M) g)
      (metricCurvatureSections (I := 𝓘(ℝ, E)) (M := M) g).ricciRealizes
      (rm04LowersRm13At_of_realizes (I := 𝓘(ℝ, E)) g (metricCov (I := 𝓘(ℝ, E)) (M := M) g)
        (metricRm13 (I := 𝓘(ℝ, E)) (M := M) g)
        (metricRm04 (I := 𝓘(ℝ, E)) (M := M) g)
        (metricCurvatureSections (I := 𝓘(ℝ, E)) (M := M) g).rm13Realizes
        (metricCurvatureSections (I := 𝓘(ℝ, E)) (M := M) g).rm04Realizes x)
      hON i i
    rw [metricRicci_apply,
      DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor (I := 𝓘(ℝ, E)) g x
        (basis i) (basis i)] at h
    simpa only [metricRm04_apply, metricRm04StandardAt_apply, Rm] using h
  have hR0 : ricciTensor (I := 𝓘(ℝ, E)) g x (basis 0) (basis 0) =
      sectionalCurvature (I := 𝓘(ℝ, E)) g x (basis 0) (basis 1) +
        sectionalCurvature (I := 𝓘(ℝ, E)) g x (basis 0) (basis 2) := by
    rw [hdiag 0, Fin.sum_univ_three, hzero 0, zero_add,
      hpair (basis 1) (basis 0) (basis 0) (basis 1), hpair (basis 2) (basis 0) (basis 0) (basis 2),
      hsec 0 1 (by decide), hsec 0 2 (by decide)]
  have hR1 : ricciTensor (I := 𝓘(ℝ, E)) g x (basis 1) (basis 1) =
      sectionalCurvature (I := 𝓘(ℝ, E)) g x (basis 0) (basis 1) +
        sectionalCurvature (I := 𝓘(ℝ, E)) g x (basis 1) (basis 2) := by
    rw [hdiag 1, Fin.sum_univ_three, hzero 1, hsec 0 1 (by decide),
      ← hpair (basis 1) (basis 2) (basis 2) (basis 1), hsec 1 2 (by decide)]
    ring
  have hR2 : ricciTensor (I := 𝓘(ℝ, E)) g x (basis 2) (basis 2) =
      sectionalCurvature (I := 𝓘(ℝ, E)) g x (basis 0) (basis 2) +
        sectionalCurvature (I := 𝓘(ℝ, E)) g x (basis 1) (basis 2) := by
    rw [hdiag 2, Fin.sum_univ_three, hzero 2, hsec 0 2 (by decide), hsec 1 2 (by decide)]
    ring
  have hsc := hscal
  rw [Fin.sum_univ_three, hR0, hR1, hR2] at hsc
  linarith

theorem ricciTensor_add_eq_sectionalCurvature_add_half_metricScalarAt_of_orthonormal
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (v w : TangentSpace 𝓘(ℝ, E) x)
    (hv : g.inner x v v = 1) (hw : g.inner x w w = 1) (hvw : g.inner x v w = 0) :
    ricciTensor (I := 𝓘(ℝ, E)) g x v v + ricciTensor (I := 𝓘(ℝ, E)) g x w w =
      sectionalCurvature (I := 𝓘(ℝ, E)) g x v w +
        metricScalarAt (I := 𝓘(ℝ, E)) g x / 2 := by
  obtain ⟨B, hB0, hB1, hBON⟩ :=
    exists_orthonormalBasis_fin_three_of_orthonormal_pair g x hdim v w hv hw hvw
  rw [← hB0, ← hB1]
  exact ricciTensor_add_eq_sectionalCurvature_add_half_metricScalarAt_of_orthonormalBasis
    g x B hBON

private theorem neg_ricciTrace_eq_neg_sectional_and_half_scalar
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (v w : TangentSpace 𝓘(ℝ, E) x)
    (hvw : g.inner x v w = 0) (heq : g.inner x v v = g.inner x w w) :
    -(ricciTensor (I := 𝓘(ℝ, E)) g x v v + ricciTensor (I := 𝓘(ℝ, E)) g x w w) =
      -(sectionalCurvature (I := 𝓘(ℝ, E)) g x v w * g.inner x v v +
        metricScalarAt (I := 𝓘(ℝ, E)) g x * g.inner x v v / 2) := by
  have hnonneg : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  rcases eq_or_lt_of_le hnonneg with hzero | hpos
  · have hv : v = 0 := by
      by_contra hv
      have hp := g.pos x v hv
      rw [← hzero] at hp
      exact absurd hp (lt_irrefl 0)
    have hw : w = 0 := by
      by_contra hw
      have hp := g.pos x w hw
      rw [← heq, ← hzero] at hp
      exact absurd hp (lt_irrefl 0)
    rw [hv, hw]
    simp
  · let c := Real.sqrt (g.inner x v v)
    have hc : c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
    have hcc : c * c = g.inner x v v := by
      rw [← pow_two, Real.sq_sqrt hpos.le]
    let e1 := c⁻¹ • v
    let e2 := c⁻¹ • w
    have hv_eq : c • e1 = v := by
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hw_eq : c • e2 = w := by
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    have he1 : g.inner x e1 e1 = 1 := by
      rw [inner_smul_smul, ← hcc]
      field_simp
    have he2 : g.inner x e2 e2 = 1 := by
      rw [inner_smul_smul, ← heq, ← hcc]
      field_simp
    have he12 : g.inner x e1 e2 = 0 := by
      rw [inner_smul_smul, hvw, mul_zero]
    have hpair := ricciTensor_add_eq_sectionalCurvature_add_half_metricScalarAt_of_orthonormal
      g x hdim e1 e2 he1 he2 he12
    have hK : sectionalCurvature (I := 𝓘(ℝ, E)) g x v w =
        sectionalCurvature (I := 𝓘(ℝ, E)) g x e1 e2 := by
      rw [← hv_eq, ← hw_eq]
      exact sectionalCurvature_smul_smul (I := 𝓘(ℝ, E)) g x hc hc e1 e2
    have hRv : ricciTensor (I := 𝓘(ℝ, E)) g x v v =
        g.inner x v v * ricciTensor (I := 𝓘(ℝ, E)) g x e1 e1 := by
      conv_lhs => rw [← hv_eq]
      rw [ricciTensor_smul_smul, hcc]
    have hRw : ricciTensor (I := 𝓘(ℝ, E)) g x w w =
        g.inner x v v * ricciTensor (I := 𝓘(ℝ, E)) g x e2 e2 := by
      conv_lhs => rw [← hw_eq]
      rw [ricciTensor_smul_smul, hcc]
    have hRic : ricciTensor (I := 𝓘(ℝ, E)) g x v v +
          ricciTensor (I := 𝓘(ℝ, E)) g x w w =
        g.inner x v v * (ricciTensor (I := 𝓘(ℝ, E)) g x e1 e1 +
          ricciTensor (I := 𝓘(ℝ, E)) g x e2 e2) := by
      rw [hRv, hRw]
      ring
    rw [hRic, hK, hpair]
    ring

end Curvature

theorem diskMapMetricVariationDensity_eq_neg_sectionalDensity_and_half_scalar_mul
    (hdim : Module.finrank ℝ E = 3)
    (hconf : DiskMapConformalAt (G t) U z)
    (hderiv : ∀ X Y : E, HasDerivAt (fun r : ℝ => (G r).inner (U z) X Y)
      (-2 * ricciTensor (I := 𝓘(ℝ, E)) (G t) (U z) X Y) t) :
    diskMapMetricVariationDensity G t U z =
      -(diskMapSectionalDensity (G t) U z +
        metricScalarAt (I := 𝓘(ℝ, E)) (G t) (U z) *
          diskMapConformalCoefficient (G t) U z / 2) := by
  rw [diskMapMetricVariationDensity_eq_neg_ricciTrace_of_hasDerivAt
    (Ric := fun y X Y => ricciTensor (I := 𝓘(ℝ, E)) (G t) y X Y) hderiv]
  rw [Curvature.neg_ricciTrace_eq_neg_sectional_and_half_scalar (G t) (U z) hdim _ _
    hconf.1 hconf.2]
  rw [diskMapSectionalDensity, diskMapConformalCoefficient]

open DifferentialGeometry.PDE.RicciFlow (SolutionOn IsSolutionOn metricDerivAt) in
theorem diskMapMetricVariationDensity_eq_neg_ricciTrace_of_isSolutionOn
    {D : RealTimeInterval} (S : SolutionOn (I := 𝓘(ℝ, E)) (M := M) D)
    (hS : IsSolutionOn (I := 𝓘(ℝ, E)) S)
    (t : RealTimeInterval.RegularTime D) (U : ℂ → M) (z : ℂ) :
    diskMapMetricVariationDensity S.family.metric (t : ℝ) U z =
      -((S.ricciAt (t : ℝ) (U z)) (vec2 (diskMapPartial U z 1) (diskMapPartial U z 1)) +
        (S.ricciAt (t : ℝ) (U z))
          (vec2 (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I))) :=
  diskMapMetricVariationDensity_eq_neg_ricciTrace_of_hasDerivAt
    (Ric := fun y X Y => (S.ricciAt (t : ℝ) y) (vec2 X Y))
    (fun X Y => metricDerivAt (I := 𝓘(ℝ, E)) S hS t (U z) X Y)

end DifferentialGeometry.Geometry
