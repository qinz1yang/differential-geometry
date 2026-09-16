import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eventually_exists_eq_height_of_mem_ray_nhds
    (ℓ : E →L[ℝ] ℝ) {x p d : E} (hlevel : ℓ x = ℓ p) (hd : ℓ d ≠ 0)
    {U : Set E} (hU : ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ y ∈ U, f y = f p ∧ dist y x < ε := by
  let t : (E →L[ℝ] ℝ) → ℝ := fun f => (f p - f x) / f d
  have htcont : ContinuousAt t ℓ :=
    ((ContinuousLinearMap.apply ℝ ℝ p).continuous.continuousAt.sub
      (ContinuousLinearMap.apply ℝ ℝ x).continuous.continuousAt).div
        (ContinuousLinearMap.apply ℝ ℝ d).continuous.continuousAt hd
  have htzero : t ℓ = 0 := by simp only [t, hlevel, sub_self, zero_div]
  have ht : Filter.Tendsto t (𝓝 ℓ) (𝓝 0) := htzero ▸ htcont.tendsto
  have hmove : Filter.Tendsto (fun u : ℝ => x + u • d) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun u : ℝ => x + u • d) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have hclose : ∀ᶠ u : ℝ in 𝓝 0, dist (x + u • d) x < ε :=
    hmove (Metric.ball_mem_nhds x hε)
  have hne : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, f d ≠ 0 :=
    (ContinuousLinearMap.apply ℝ ℝ d).continuous.continuousAt.preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds hd)
  filter_upwards [ht hU, ht hclose, hne] with f hfU hfclose hfne
  refine ⟨x + t f • d, hfU, ?_, hfclose⟩
  rw [map_add, map_smul, smul_eq_mul]
  dsimp only [t]
  rw [div_mul_cancel₀ _ hfne]
  ring

theorem eventually_exists_mem_openSimplex_eq_height
    (ℓ : E →L[ℝ] ℝ) {s : Finset E} {x p d : E} (hx : x ∈ openSimplex s)
    (hd : d ∈ vectorSpan ℝ (s : Set E)) (hlevel : ℓ x = ℓ p) (hℓd : ℓ d ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ y ∈ openSimplex s, f y = f p ∧ dist y x < ε :=
  eventually_exists_eq_height_of_mem_ray_nhds ℓ hlevel hℓd
    (eventually_mem_openSimplex_of_mem_vectorSpan hx hd) hε

theorem eventually_exists_mem_carrierFace_eq_height_of_unique_vertex_in_fiber
    (K : Geometry.SimplicialComplex ℝ E) (ℓ : E →L[ℝ] ℝ) {p x : E}
    (hunique : ∀ v ∈ K.vertices, ℓ v = ℓ p → v = p)
    (hx : x ∈ K.space) (hlevel : ℓ x = ℓ p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ,
      ∃ y ∈ openSimplex (carrierFace K x), f y = f p ∧ dist y x < ε ∧ (x ∈ K.vertices → y = x) := by
  classical
  by_cases hxp : x = p
  · subst x
    exact Filter.Eventually.of_forall fun _ =>
      ⟨p, mem_openSimplex_carrierFace hx, rfl, by simpa only [dist_self] using hε, fun _ => rfl⟩
  have hxv : x ∉ K.vertices := fun hxv => hxp (hunique x hxv hlevel)
  have hs := carrierFace_mem hx
  have hxs := mem_openSimplex_carrierFace hx
  have hvert : ∀ v ∈ carrierFace K x, v ∈ K.vertices := fun v hv =>
    K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hex : ∃ v ∈ carrierFace K x, ℓ v ≠ ℓ p := by
    by_contra! hz
    have hsub : (carrierFace K x : Set E) ⊆ {p} := fun v hv => hunique v (hvert v hv) (hz v hv)
    exact hxp (convexHull_min hsub (convex_singleton p) (openSimplex_subset_convexHull _ hxs))
  obtain ⟨v, hv, hvl⟩ := hex
  have hd : v - x ∈ vectorSpan ℝ (carrierFace K x : Set E) := by
    simpa only [direction_affineSpan, vsub_eq_sub] using
      AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hv)
        (convexHull_subset_affineSpan _ (openSimplex_subset_convexHull _ hxs))
  have hℓd : ℓ (v - x) ≠ 0 := by
    rw [map_sub, hlevel]
    exact sub_ne_zero.mpr hvl
  filter_upwards [eventually_exists_mem_openSimplex_eq_height ℓ hxs hd hlevel hℓd hε] with f hf
  obtain ⟨y, hy, hfy, hyclose⟩ := hf
  exact ⟨y, hy, hfy, hyclose, fun h => (hxv h).elim⟩

theorem eventually_exists_mem_carrierFace_eq_height
    (K : Geometry.SimplicialComplex ℝ E) (ℓ : E →L[ℝ] ℝ) (hinj : InjOn ℓ K.vertices)
    {p x : E} (hp : p ∈ K.vertices) (hx : x ∈ K.space) (hlevel : ℓ x = ℓ p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ,
      ∃ y ∈ openSimplex (carrierFace K x), f y = f p ∧ dist y x < ε ∧ (x ∈ K.vertices → y = x) :=
  eventually_exists_mem_carrierFace_eq_height_of_unique_vertex_in_fiber K ℓ
    (fun _ hv h => hinj hv hp h) hx hlevel hε

theorem eventually_exists_vertexMap_eq_height_on_fiber_of_unique_vertex_in_fiber
    (K : Geometry.SimplicialComplex ℝ E) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {p : E} (hunique : ∀ v ∈ K.vertices, ℓ v = ℓ p → v = p)
    {A : Set E} (hA : A.Finite) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ φ : E → E,
      EqOn φ id Aᶜ ∧ EqOn φ id K.vertices ∧ EqOn φ id {x | ℓ x ≠ ℓ p} ∧
      (∀ v ∈ A, dist (φ v) v < ε) ∧
      (∀ v ∈ A, ℓ v = ℓ p → f (φ v) = f p) ∧
      ∀ v ∈ A ∩ K.space, φ v ∈ openSimplex (carrierFace K v) := by
  classical
  have hdir : ∃ d : E, ℓ d ≠ 0 := by
    by_contra! h
    exact hℓ (by ext d; exact h d)
  obtain ⟨d, hd⟩ := hdir
  let R : (E →L[ℝ] ℝ) → E → E → Prop := fun f v y =>
    dist y v < ε ∧ (ℓ v = ℓ p → f y = f p) ∧
      (v ∈ K.space → y ∈ openSimplex (carrierFace K v)) ∧
      (ℓ v ≠ ℓ p ∨ v ∈ K.vertices → y = v)
  have hpoint : ∀ v : E, ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ y, R f v y := by
    intro v
    by_cases hvlevel : ℓ v = ℓ p
    · by_cases hvK : v ∈ K.space
      · filter_upwards [eventually_exists_mem_carrierFace_eq_height_of_unique_vertex_in_fiber K ℓ hunique hvK hvlevel hε] with f hf
        obtain ⟨y, hy, hfy, hyclose, hyfix⟩ := hf
        exact ⟨y, hyclose, fun _ => hfy, fun _ => hy,
          fun h => hyfix (h.resolve_left (not_not.mpr hvlevel))⟩
      · filter_upwards [eventually_exists_eq_height_of_mem_ray_nhds ℓ hvlevel hd
          (U := univ) (Filter.Eventually.of_forall fun _ => mem_univ _) hε] with f hf
        obtain ⟨y, -, hfy, hyclose⟩ := hf
        refine ⟨y, hyclose, fun _ => hfy, fun h => (hvK h).elim, ?_⟩
        intro h
        exact (hvK (K.vertices_subset_space (h.resolve_left (not_not.mpr hvlevel)))).elim
    · exact Filter.Eventually.of_forall fun _ =>
        ⟨v, by simpa only [dist_self] using hε, fun h => (hvlevel h).elim,
          fun h => mem_openSimplex_carrierFace h, fun _ => rfl⟩
  let _ : Finite A := hA.to_subtype
  have hall : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∀ v : A, ∃ y, R f v y :=
    Filter.eventually_all.mpr (fun v => hpoint v)
  filter_upwards [hall] with f hf
  let φ : E → E := fun v => if hv : v ∈ A then Classical.choose (hf ⟨v, hv⟩) else v
  have hφ : ∀ v ∈ A, R f v (φ v) := by
    intro v hv
    simpa only [φ, dif_pos hv] using Classical.choose_spec (hf ⟨v, hv⟩)
  have hfix : ∀ v ∉ A, φ v = v := fun v hv => dif_neg hv
  refine ⟨φ, fun v hv => hfix v hv, ?_, ?_, fun v hv => (hφ v hv).1,
    fun v hv => (hφ v hv).2.1, fun v hv => (hφ v hv.1).2.2.1 hv.2⟩
  · intro v hvK
    by_cases hv : v ∈ A
    · exact (hφ v hv).2.2.2 (Or.inr hvK)
    · exact hfix v hv
  · intro v hvlevel
    by_cases hv : v ∈ A
    · exact (hφ v hv).2.2.2 (Or.inl hvlevel)
    · exact hfix v hv

theorem eventually_exists_vertexMap_eq_height_on_fiber
    (K : Geometry.SimplicialComplex ℝ E) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ K.vertices)
    {A : Set E} (hA : A.Finite) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ φ : E → E,
      EqOn φ id Aᶜ ∧ EqOn φ id K.vertices ∧ EqOn φ id {x | ℓ x ≠ ℓ p} ∧
      (∀ v ∈ A, dist (φ v) v < ε) ∧
      (∀ v ∈ A, ℓ v = ℓ p → f (φ v) = f p) ∧
      ∀ v ∈ A ∩ K.space, φ v ∈ openSimplex (carrierFace K v) :=
  eventually_exists_vertexMap_eq_height_on_fiber_of_unique_vertex_in_fiber K ℓ hℓ
    (fun _ hv h => hinj hv hp h) hA hε

theorem eventually_exists_isPLHomeomorphOn_move_fiber_vertices_of_unique_vertex_in_fiber [FiniteDimensional ℝ E]
    (K R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {p : E} (hunique : ∀ v ∈ K.vertices, ℓ v = ℓ p → v = p) {U : Set E} (hU : IsOpen U) (hRU : R.space ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ h : E → E,
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      EqOn h id (R.vertices ∩ K.vertices) ∧ EqOn h id (R.vertices ∩ {x | ℓ x ≠ ℓ p}) ∧
      (∀ v ∈ R.vertices, ℓ v = ℓ p → f (h v) = f p) ∧
      (∀ v ∈ R.vertices ∩ K.space, h v ∈ openSimplex (carrierFace K v)) ∧
      ∀ s ∈ R.faces, ∃ a : E →ᵃ[ℝ] E, EqOn h a (convexHull ℝ (s : Set E)) := by
  obtain ⟨δ, hδ, hext⟩ := exists_isPLHomeomorphOn_extension_of_small_vertex_perturbation R hU hRU hε
  have hRfin : R.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite R.faces)
  filter_upwards [eventually_exists_vertexMap_eq_height_on_fiber_of_unique_vertex_in_fiber K ℓ hℓ hunique hRfin hδ] with f hf
  obtain ⟨φ, -, hfixK, hfixLevel, hclose, hlevel, hcarrier⟩ := hf
  obtain ⟨h, hh, hhclose, hhfix, hhφ⟩ := hext φ hclose
  have hvertices : EqOn h φ R.vertices := by
    intro v hv
    rw [hhφ (R.vertices_subset_space hv), simplicialMap_vertex R φ hv]
  refine ⟨h, hh, hhclose, hhfix, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact (hvertices hv.1).trans (hfixK hv.2)
  · intro v hv
    exact (hvertices hv.1).trans (hfixLevel hv.2)
  · intro v hv hvlevel
    rw [hvertices hv]
    exact hlevel v hv hvlevel
  · intro v hv
    rw [hvertices hv.1]
    exact hcarrier v hv
  · intro s hs
    obtain ⟨a, ha⟩ := exists_affineMap_eqOn_simplicialMap R φ hs
    exact ⟨a, (hhφ.mono (R.convexHull_subset_space hs)).trans ha⟩

theorem eventually_exists_isPLHomeomorphOn_move_fiber_vertices [FiniteDimensional ℝ E]
    (K R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ K.vertices) {U : Set E} (hU : IsOpen U) (hRU : R.space ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ h : E → E,
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      EqOn h id (R.vertices ∩ K.vertices) ∧ EqOn h id (R.vertices ∩ {x | ℓ x ≠ ℓ p}) ∧
      (∀ v ∈ R.vertices, ℓ v = ℓ p → f (h v) = f p) ∧
      (∀ v ∈ R.vertices ∩ K.space, h v ∈ openSimplex (carrierFace K v)) ∧
      ∀ s ∈ R.faces, ∃ a : E →ᵃ[ℝ] E, EqOn h a (convexHull ℝ (s : Set E)) :=
  eventually_exists_isPLHomeomorphOn_move_fiber_vertices_of_unique_vertex_in_fiber K R ℓ hℓ
    (fun _ hv h => hinj hv hp h) hU hRU hε

end DifferentialGeometry.Topology.PiecewiseLinear
