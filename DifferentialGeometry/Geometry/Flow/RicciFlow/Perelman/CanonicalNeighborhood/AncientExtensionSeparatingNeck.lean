import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FarPointSeparatingNeckFrontier

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]

omit [IsManifold I3 ∞ M] in
theorem TransversePath.start_not_mem {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) : p ∉ sphere := by
  intro hp
  have h0 : (0 : ℝ) ∈ c.crossings :=
    (c.crossings_eq 0 ⟨le_rfl, zero_le_one⟩).mp (by simpa only [c.start] using hp)
  exact absurd (c.crossings_interior 0 h0).1 (lt_irrefl 0)

omit [IsManifold I3 ∞ M] in
theorem TransversePath.finish_not_mem {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) : z ∉ sphere := by
  intro hz
  have h1 : (1 : ℝ) ∈ c.crossings :=
    (c.crossings_eq 1 ⟨zero_le_one, le_rfl⟩).mp (by simpa only [c.finish] using hz)
  exact absurd (c.crossings_interior 1 h1).2 (lt_irrefl 1)

theorem SpatialNeck.strip_subset_source {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M}
    (neck : SpatialNeck g eps x) :
    Set.univ ×ˢ Set.Icc (-1 : ℝ) 1 ⊆ neck.map.source := by
  refine (Set.prod_mono (subset_refl _) ?_).trans neck.domain
  intro t ht
  have hone : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ neck.eps_pos).mpr (by linarith [neck.eps_small])
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem SpatialNeck.centralSlice_eq_range {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M}
    (neck : SpatialNeck g eps x) :
    neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)) =
      Set.range (fun c : Sphere 2 => neck.map (c, (0 : ℝ))) := by
  ext w
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq2 : q.2 = 0 := Set.mem_singleton_iff.mp hq.2
    refine ⟨q.1, ?_⟩
    conv_lhs => rw [← hq2]
  · rintro ⟨c, rfl⟩
    exact ⟨(c, 0), ⟨trivial, rfl⟩, rfl⟩

theorem SpatialNeck.not_isPreconnected_compl_of_not_mem_connectedComponentIn
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x p z : M} (neck : SpatialNeck g eps x)
    (hp : p ∈ (neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)))ᶜ)
    (hz : z ∈ (neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)))ᶜ)
    (hzp : z ∉ connectedComponentIn (neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)))ᶜ p) :
    ¬ IsPreconnected (neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)))ᶜ := by
  intro hpre
  exact hzp (by rw [hpre.connectedComponentIn hp]; exact hz)

theorem normalizedSequence_false_of_sigma_nonpos {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsigma : sigma ≤ 0) (X : NormalizedSequence.{u} eps kappa sigma Phi) : False := by
  have h := (X.noncollapse 0).1
  have hle : Real.sqrt (X.scale 0) * sigma ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) hsigma
  exact absurd h (not_lt.mpr hle)

theorem farPointSeparatingNeckInput_of_sigma_nonpos {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsigma : sigma ≤ 0) : FarPointSeparatingNeckInput.{u} kappa sigma Phi := by
  refine ⟨1, one_pos, fun eps _ _ X _ _ _ _ _ _ _ _ => ?_⟩
  exact (normalizedSequence_false_of_sigma_nonpos hsigma X).elim

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
