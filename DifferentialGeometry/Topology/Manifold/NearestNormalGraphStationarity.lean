import DifferentialGeometry.Topology.Manifold.NearestPointStationarity
import DifferentialGeometry.Topology.Embedding.Lift
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphStationarity

/-! Actual embedding normality implies the normal equation in a genuine graph parametrization. -/

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped ContDiff Manifold Topology
namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {k : ℕ} {Z : Set H} [ChartedSpace (Fin k → ℝ) Z]

theorem parametrization_derivative_mem_actual_tangent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hemb : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
      (Subtype.val : Z → H))
    (U : TopologicalSpace.Opens E) (f : U → H)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ∞ f) (hrange : ∀ x, f x ∈ Z)
    (x : U) (v : E) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) f x v ∈
      actualZeroSetTangentSpace k Z ⟨f x, hrange x⟩ := by
  have hr : range f ⊆ range (Subtype.val : Z → H) := by
    rintro w ⟨a, rfl⟩
    exact ⟨⟨f a, hrange a⟩, rfl⟩
  let q : U → Z := hemb.lift f hr
  have hq := hemb.contMDiff_lift hf hr
  have heq : (Subtype.val : Z → H) ∘ q = f := funext (hemb.comp_lift hr)
  have hx : q x = ⟨f x, hrange x⟩ := Subtype.ext (hemb.comp_lift hr x)
  have hc := mfderiv_comp x (hemb.contMDiff.mdifferentiableAt (by simp))
    (hq.mdifferentiableAt (by simp))
  rw [heq] at hc
  rw [← hx]
  refine ⟨mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) q x v, ?_⟩
  exact (congrArg (fun A : E →L[ℝ] H => A v) hc).symm

theorem normal_equation_of_actual_normal_graph
    (hemb : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
      (Subtype.val : Z → H))
    (L : Submodule ℝ H) [CompleteSpace L] [CompleteSpace Lᗮ]
    (o : H) (g : L → Lᗮ) (U : TopologicalSpace.Opens L)
    (hg : ContDiffOn ℝ ∞ g U)
    (hgraph : ∀ s ∈ U, o + orthogonalCoordinateSum L (s, g s) ∈ Z)
    (t : U) (y : Z) (hy : (y : H) = o + orthogonalCoordinateSum L (t, g t))
    (z : H) (hn : z - (y : H) ∈ (actualZeroSetTangentSpace k Z y)ᗮ) :
    (t : L) - L.orthogonalProjectionOnto (z - o) +
      (ContinuousLinearMap.adjoint (fderiv ℝ g t))
        (g t - Lᗮ.orthogonalProjectionOnto (z - o)) = 0 := by
  let f : L → H := fun s => o + orthogonalCoordinateSum L (s, g s)
  have hdf : ContDiffOn ℝ ∞ f U :=
    contDiffOn_const.add ((orthogonalCoordinateSum L).contDiff.comp_contDiffOn
      (contDiffOn_id.prodMk hg))
  have hsf : ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, H) ∞ (fun s : U => f s) := by
    intro s
    exact contMDiffAt_subtype_iff.mpr
      ((hdf.contDiffAt (U.isOpen.mem_nhds s.property)).contMDiffAt)
  have hdg := (hg.contDiffAt (U.isOpen.mem_nhds t.property)).differentiableAt (by simp)
  have hd : HasFDerivAt f
      ((orthogonalCoordinateSum L).comp
        ((ContinuousLinearMap.id ℝ L).prod (fderiv ℝ g t))) t := by
    exact ((orthogonalCoordinateSum L).hasFDerivAt.comp (t : L)
      ((hasFDerivAt_id (t : L)).prodMk hdg.hasFDerivAt)).const_add o
  have htan (v : L) : (v : H) + (fderiv ℝ g t v : H) ∈
      actualZeroSetTangentSpace k Z y := by
    have hh := parametrization_derivative_mem_actual_tangent hemb U
      (fun s : U => f s) hsf (fun s => hgraph s s.property) t v
    have hy' : (⟨f t, hgraph t t.property⟩ : Z) = y := Subtype.ext hy.symm
    rw [hy', DifferentialGeometry.mfderiv_restrict_open f U t, mfderiv_eq_fderiv,
      hd.fderiv] at hh
    exact hh
  let w : L := (t : L) - L.orthogonalProjectionOnto (z - o) +
    (ContinuousLinearMap.adjoint (fderiv ℝ g t))
      (g t - Lᗮ.orthogonalProjectionOnto (z - o))
  have hz : z - o = (L.orthogonalProjectionOnto (z - o) : H) +
      (Lᗮ.orthogonalProjectionOnto (z - o) : H) :=
    (L.starProjection_add_starProjection_orthogonal (z - o)).symm
  have hres : (y : H) - z = (((t : L) - L.orthogonalProjectionOnto (z - o) : L) : H) +
      ((g t - Lᗮ.orthogonalProjectionOnto (z - o) : Lᗮ) : H) := by
    calc
      (y : H) - z = ((t : H) + (g t : H)) - (z - o) := by
        rw [hy]
        change o + ((t : H) + (g t : H)) - z = _
        abel
      _ = _ := by
        nth_rw 1 [hz]
        change ((t : H) + (g t : H)) - (_ + _) = ((t : H) - _) + ((g t : H) - _)
        abel
  have hi : inner ℝ ((y : H) - z) ((w : H) + (fderiv ℝ g t w : H)) = 0 := by
    rw [Submodule.mem_orthogonal'] at hn
    have hh := hn _ (htan w)
    have hneg : (y : H) - z = -(z - (y : H)) := by abel
    rw [hneg, inner_neg_left, hh, neg_zero]
  have hi' : inner ℝ w w = 0 := by
    rw [hres, inner_add_left, inner_add_right, inner_add_right,
      Submodule.inner_right_of_mem_orthogonal (K := L)
        ((t : L) - L.orthogonalProjectionOnto (z - o)).property
        (fderiv ℝ g t w).property,
      Submodule.inner_left_of_mem_orthogonal (K := L) w.property
        (g t - Lᗮ.orthogonalProjectionOnto (z - o)).property] at hi
    change inner ℝ ((t : L) - L.orthogonalProjectionOnto (z - o)) w + 0 +
      (0 + inner ℝ (g t - Lᗮ.orthogonalProjectionOnto (z - o)) (fderiv ℝ g t w)) = 0 at hi
    change inner ℝ ((t : L) - L.orthogonalProjectionOnto (z - o) +
      (ContinuousLinearMap.adjoint (fderiv ℝ g t))
        (g t - Lᗮ.orthogonalProjectionOnto (z - o))) w = 0
    rw [inner_add_left, ContinuousLinearMap.adjoint_inner_left]
    simpa only [add_zero, zero_add] using hi
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp hi'

end GC.MetricGeometry
