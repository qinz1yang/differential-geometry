import DifferentialGeometry.Topology.PiecewiseLinear.CarrierInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.HeightProjection

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem eventually_exists_isPLHomeomorphOn_preserving_sphere_move_fiber {n : ℕ}
    (K L R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hK : IsPLSphere (n + 1) K.space) (hLK : IsSubdivision L K) (hLR : L ≤ R)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ K.vertices)
    {U : Set E} (hU : IsOpen U) (hRU : R.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ h : E → E,
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      EqOn h id K.vertices ∧ h '' K.space = K.space ∧
      (∀ s ∈ R.faces, (∀ v ∈ s, ℓ v = ℓ p) →
        MapsTo h (convexHull ℝ (s : Set E)) {x | f x = f p}) ∧
      ∀ s ∈ R.faces, ∃ a : E →ᵃ[ℝ] E, EqOn h a (convexHull ℝ (s : Set E)) := by
  filter_upwards [eventually_exists_isPLHomeomorphOn_move_fiber_vertices K R ℓ hℓ hinj hp hU hRU hε]
    with f hf
  obtain ⟨h, hh, hclose, hfix, hfixK, -, hlevel, hcarrier, hfaces⟩ := hf
  have hcarL : ∀ v ∈ L.vertices, h v ∈ convexHull ℝ (carrierFace K v : Set E) := by
    intro v hv
    exact openSimplex_subset_convexHull _ (hcarrier v
      ⟨hLR hv, hLK.space_eq.subset (L.vertices_subset_space hv)⟩)
  have himage : h '' K.space = K.space := image_space_eq_of_mem_carrierFace K L hK hLK
    (hh.isPiecewiseAffineOn.continuousOn.mono (subset_univ _))
    (hh.bijOn.injOn.mono (subset_univ _)) (fun s hs => hfaces s (hLR hs)) hcarL
  refine ⟨h, hh, hclose, hfix, fun v hv => hfixK ⟨hLR (hLK.singleton_mem hv), hv⟩, himage, ?_, hfaces⟩
  intro s hs hslevel x hx
  obtain ⟨a, ha⟩ := hfaces s hs
  rw [ha hx]
  have hverts : (s : Set E) ⊆ a ⁻¹' {y | f y = f p} := by
    intro v hv
    change f (a v) = f p
    rw [← ha (subset_convexHull ℝ _ hv)]
    exact hlevel v (R.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
      (hslevel v hv)
  exact convexHull_min hverts
    (((convex_singleton (f p)).linear_preimage f.toLinearMap).affine_preimage a) hx

end DifferentialGeometry.Topology.PiecewiseLinear
