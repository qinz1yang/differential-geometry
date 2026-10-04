import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryMap
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryTopology

noncomputable section

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {G : Type*} [Group G]
  [MulAction G (Hyperboloid E)] [IsIsometricSMul G (Hyperboloid E)]
  [MulAction G (Hyperboloid E')] [IsIsometricSMul G (Hyperboloid E')]

omit [FiniteDimensional ℝ E'] in
private theorem continuous_boundary_isometry_conjugate
    (f : C(Metric.sphere (0 : E) 1, Metric.sphere (0 : E') 1)) :
    Continuous (fun p : (Hyperboloid E' ≃ᵢ Hyperboloid E') × (Hyperboloid E ≃ᵢ Hyperboloid E) =>
      (boundaryHomeomorph p.1 : C(Metric.sphere (0 : E') 1, Metric.sphere (0 : E') 1)).comp
        (f.comp (boundaryHomeomorph p.2 : C(Metric.sphere (0 : E) 1, Metric.sphere (0 : E) 1)))) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  let P := (Hyperboloid E' ≃ᵢ Hyperboloid E') × (Hyperboloid E ≃ᵢ Hyperboloid E)
  have hpair : Continuous (fun p : P × Metric.sphere (0 : E) 1 => (p.1.2, p.2)) :=
    continuous_fst.snd.prodMk continuous_snd
  have hright := (continuous_boundaryHomeomorph_apply (E := E) (F := E)).comp hpair
  have hmid := f.continuous.comp hright
  have hfirst : Continuous (fun p : P × Metric.sphere (0 : E) 1 => p.1.1) :=
    continuous_fst.fst
  have hpair' := hfirst.prodMk hmid
  have hout := (continuous_boundaryHomeomorph_apply (E := E') (F := E')).comp hpair'
  exact hout


theorem tendsto_boundaryMap_isometry_orbit_conjugate
    (F : C(Hyperboloid E, Hyperboloid E'))
    (hdist : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (F x) (F y) ∧ dist (F x) (F y) ≤ L * dist x y + C)
    (hF : ∀ (γ : G) (x : Hyperboloid E), F (γ • x) = γ • F x)
    (a : ℕ → Hyperboloid E' ≃ᵢ Hyperboloid E')
    (b : ℕ → Hyperboloid E ≃ᵢ Hyperboloid E) (γ : ℕ → G) (k : ℕ → ℕ)
    (A : Hyperboloid E' ≃ᵢ Hyperboloid E') (B : Hyperboloid E ≃ᵢ Hyperboloid E)
    (hA : Filter.Tendsto (fun n => (a (k n) *
      (IsometryEquiv.constSMul (γ (k n)) : Hyperboloid E' ≃ᵢ Hyperboloid E').symm :
        C(Hyperboloid E', Hyperboloid E'))) Filter.atTop (𝓝 (A : C(Hyperboloid E', Hyperboloid E'))))
    (hB : Filter.Tendsto (fun n => ((IsometryEquiv.constSMul (γ (k n)) :
      Hyperboloid E ≃ᵢ Hyperboloid E) * b (k n) : C(Hyperboloid E, Hyperboloid E)))
        Filter.atTop (𝓝 (B : C(Hyperboloid E, Hyperboloid E)))) :
    Filter.Tendsto (fun n =>
      (boundaryHomeomorph (a (k n)) : C(Metric.sphere (0 : E') 1, Metric.sphere (0 : E') 1)).comp
        ((boundaryMap F hdist).comp
          (boundaryHomeomorph (b (k n)) : C(Metric.sphere (0 : E) 1, Metric.sphere (0 : E) 1))))
      Filter.atTop (𝓝
        ((boundaryHomeomorph A : C(Metric.sphere (0 : E') 1, Metric.sphere (0 : E') 1)).comp
          ((boundaryMap F hdist).comp
            (boundaryHomeomorph B : C(Metric.sphere (0 : E) 1, Metric.sphere (0 : E) 1))))) := by
  let U (n : ℕ) : Hyperboloid E' ≃ᵢ Hyperboloid E' :=
    a n * (IsometryEquiv.constSMul (γ n) : Hyperboloid E' ≃ᵢ Hyperboloid E').symm
  let V (n : ℕ) : Hyperboloid E ≃ᵢ Hyperboloid E :=
    (IsometryEquiv.constSMul (γ n) : Hyperboloid E ≃ᵢ Hyperboloid E) * b n
  have hU : Filter.Tendsto (fun n => U (k n)) Filter.atTop (𝓝 A) :=
    IsometryEquiv.isEmbedding_toContinuousMap.tendsto_nhds_iff.mpr hA
  have hV : Filter.Tendsto (fun n => V (k n)) Filter.atTop (𝓝 B) :=
    IsometryEquiv.isEmbedding_toContinuousMap.tendsto_nhds_iff.mpr hB
  let T (p : (Hyperboloid E' ≃ᵢ Hyperboloid E') × (Hyperboloid E ≃ᵢ Hyperboloid E)) :=
    (boundaryHomeomorph p.1 : C(Metric.sphere (0 : E') 1, Metric.sphere (0 : E') 1)).comp
      ((boundaryMap F hdist).comp
        (boundaryHomeomorph p.2 : C(Metric.sphere (0 : E) 1, Metric.sphere (0 : E) 1)))
  have hT : Continuous T := continuous_boundary_isometry_conjugate (boundaryMap F hdist)
  have hlim := (hT.tendsto (A, B)).comp (hU.prodMk_nhds hV)
  apply hlim.congr'
  apply Filter.Eventually.of_forall
  intro n
  apply ContinuousMap.ext
  intro ξ
  change boundaryHomeomorph (U (k n))
    (boundaryMap F hdist (boundaryHomeomorph (V (k n)) ξ)) = _
  have hleft : U (k n) =
      (IsometryEquiv.constSMul (γ (k n)) : Hyperboloid E' ≃ᵢ Hyperboloid E').symm.trans (a (k n)) := rfl
  have hright : V (k n) = (b (k n)).trans
      (IsometryEquiv.constSMul (γ (k n)) : Hyperboloid E ≃ᵢ Hyperboloid E) := rfl
  rw [hleft, hright, boundaryHomeomorph_trans, boundaryHomeomorph_trans]
  simp only [Homeomorph.trans_apply]
  rw [boundaryMap_smul F hdist id hF (γ (k n)), ← boundaryHomeomorph_symm]
  simp only [id_eq, Homeomorph.symm_apply_apply, ContinuousMap.comp_apply, ContinuousMap.coe_apply]

end DifferentialGeometry.Hyperboloid
