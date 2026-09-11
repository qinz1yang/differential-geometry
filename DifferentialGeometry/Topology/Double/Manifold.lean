import DifferentialGeometry.Topology.Double.SmoothAtlas
import DifferentialGeometry.Topology.Double.SmoothCopies
import DifferentialGeometry.Topology.Manifold.Boundary.DefiningCollar

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology TopologicalSpace
open scoped ContDiff Topology
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
namespace DifferentialGeometry.Topology

theorem exists_smoothAtlas_intrinsicDouble
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [CompactSpace M] :
    ∃ A : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1)))
        (Double ((𝓡∂ (n + 1)).boundary M)), let _ := A
      IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
        (Double ((𝓡∂ (n + 1)).boundary M)) ∧
      T2Space (Double ((𝓡∂ (n + 1)).boundary M)) ∧
      ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
        (doublePositive ((𝓡∂ (n + 1)).boundary M)) ∧
      ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
        (doubleNegative ((𝓡∂ (n + 1)).boundary M)) := by
  let I := 𝓡∂ (n + 1)
  let J := HasSmoothBoundary.boundaryModel I
  let _ : ChartedSpace (HasSmoothBoundary.boundaryH I) (I.boundary M) :=
    inferInstanceAs (ChartedSpace (HasSmoothBoundary.boundaryH I) (BoundaryManifold I M))
  let _ : IsManifold J ∞ (I.boundary M) := inferInstanceAs (IsManifold J ∞ (BoundaryManifold I M))
  obtain ⟨r, _, hn, hzero, a, ha, c, hc, _, _, hheight, hrange, Y, hY, d, hd⟩ :=
    DifferentialGeometry.Manifold.Boundary.exists_definingFunction_sublevel_collar (n := n) (M := M)
  let _ : Fact ((0 : ℝ) < a) := ⟨ha⟩
  have hr (b : (I.boundary M)) : r b.val = 0 := (hzero b.val).mpr b.property
  have hz (x : M) (hx : r x = 0) : x ∈ (I.boundary M) := (hzero x).mp hx
  have hsmall (x : M) (hx : r x ≤ a) : x ∈ range c := by rw [hrange]; exact hx
  have hI (x : M) (hx : 0 < r x) : I.IsInteriorPoint x :=
    (I.isInteriorPoint_iff_not_isBoundaryPoint x).mpr (fun hb => hx.ne' ((hzero x).mpr hb))
  have hdim : Module.finrank ℝ (HasSmoothBoundary.boundaryE I × ℝ) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [Module.finrank_prod, Module.finrank_self]
    exact HasSmoothBoundary.finrank_boundaryE_succ
  let L : (HasSmoothBoundary.boundaryE I × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq hdim
  obtain ⟨d', hd'⟩ := DifferentialGeometry.Manifold.BoundaryCollar.exists_positiveCoordinates_diffeomorph
    J I r c hheight Y hY d hd
  have hboundary : IsManifold J ∞ (I.boundary M) := by infer_instance
  obtain ⟨A, hA, hp, hm, hs⟩ := @exists_smoothAtlas_double_of_collar M (EuclideanSpace ℝ (Fin (n + 1)))
    (EuclideanHalfSpace (n + 1)) (HasSmoothBoundary.boundaryE I) (HasSmoothBoundary.boundaryH I)
    _ _ _ _ _ _ _ I _ (I.boundary M) _ _ _ _ J hboundary _ L r hr hz hn hI a c hheight
    hsmall hc.isEmbedding ha d' hd'
  let _ := A
  have hcopies := contMDiff_double_copies_of_collar I (I.boundary M) J r hr hz hn c hheight hsmall hc.isEmbedding
    ha Y hY d hd hp hm (fun b => (hs b).1)
  exact ⟨A, hA, t2Space_double (I.boundary M) r hr hz, hcopies⟩

end DifferentialGeometry.Topology
