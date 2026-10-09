import DifferentialGeometry.Topology.Compactness.EventualInjectivity
import DifferentialGeometry.Topology.UniformConvergence.Injectivity
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph

set_option autoImplicit false

noncomputable section
open Set Filter Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E F H G X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace X] [ChartedSpace H X]
  [FirstCountableTopology X] [Nonempty X]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {Y : ℕ → Type*} [∀ n, TopologicalSpace (Y n)] [∀ n, ChartedSpace G (Y n)]

theorem eventually_exists_partialDiffeomorph_of_collision_limits
    {K S : Set X} (hK : IsCompact K) (hS : IsOpen S) (hSK : S ⊆ K)
    (f : ∀ n, X → Y n) (r : ℕ∞ω)
    (hregular : ∀ᶠ n in atTop, IsLocalDiffeomorphOn I J r (f n) S)
    (hlocal : ∀ x ∈ K, ∃ V ∈ 𝓝 x, ∀ᶠ n in atTop, InjOn (f n) V)
    (hcollision : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ (x y : ℕ → X), (∀ n, x n ∈ K) → (∀ n, y n ∈ K) →
      ∀ a ∈ K, ∀ b ∈ K,
        Tendsto x atTop (𝓝 a) → Tendsto y atTop (𝓝 b) →
        (∀ n, f (φ n) (x n) = f (φ n) (y n)) → a = b) :
    ∀ᶠ n in atTop, ∃ d : PartialDiffeomorph I J X (Y n) r,
      d.source = S ∧ d.target = f n '' S ∧ (d : X → Y n) = f n := by
  have hinj := hK.eventually_injOn_of_local_injOn_of_collision_limits f hlocal hcollision
  filter_upwards [hregular, hinj] with n hn hi
  exact exists_partialDiffeomorph_of_injOn hS hn (hi.mono hSK)

omit [FirstCountableTopology X] in
theorem eventually_exists_partialDiffeomorph_of_tendstoLocallyUniformlyOn_comp
    {ι Z : Type*} [UniformSpace Z] [T2Space Z]
    {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace G (M i)]
    {l : Filter ι} {K S : Set X} (hK : IsCompact K) (hS : IsOpen S) (hSK : S ⊆ K)
    (f : ∀ i, X → M i) (q : ∀ i, M i → Z) (r : ℕ∞ω)
    (hregular : ∀ᶠ i in l, IsLocalDiffeomorphOn I J r (f i) S)
    (hlocal : ∀ x ∈ K, ∃ V ∈ 𝓝[K] x, ∀ᶠ i in l, InjOn (f i) V)
    {g : X → Z}
    (hconv : TendstoLocallyUniformlyOn (fun i x ↦ q i (f i x)) g l K)
    (hg : ContinuousOn g K) (hinj : InjOn g K) :
    ∀ᶠ i in l, ∃ d : PartialDiffeomorph I J X (M i) r,
      d.source = S ∧ d.target = f i '' S ∧ (d : X → M i) = f i := by
  have hi := hK.eventually_injOn_of_local_injOn_of_tendstoLocallyUniformlyOn_comp
    f q hlocal hconv hg hinj
  filter_upwards [hregular, hi] with i hregulari hii
  exact exists_partialDiffeomorph_of_injOn hS hregulari (hii.mono hSK)

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.Manifold

theorem eventually_exists_partialDiffeomorph_of_local_diffeomorphs
    {E F H G X Z ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace X] [ChartedSpace H X]
    [Nonempty X] [UniformSpace Z] [T2Space Z]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace G (M i)]
    {l : Filter ι} {K S : Set X} (hK : IsCompact K) (hS : IsOpen S) (hSK : S ⊆ K)
    (f : ∀ i, X → M i) (q : ∀ i, M i → Z) (r : ℕ∞ω)
    (hlocal : ∀ x ∈ K, ∃ V ∈ 𝓝 x, ∀ᶠ i in l,
      IsLocalDiffeomorphOn I J r (f i) V ∧ InjOn (f i) V)
    {g : X → Z}
    (hconv : TendstoLocallyUniformlyOn (fun i x ↦ q i (f i x)) g l K)
    (hg : ContinuousOn g K) (hinj : InjOn g K) :
    ∀ᶠ i in l, ∃ d : PartialDiffeomorph I J X (M i) r,
      d.source = S ∧ d.target = f i '' S ∧ (d : X → M i) = f i := by
  have hregular : ∀ᶠ i in l, IsLocalDiffeomorphOn I J r (f i) S := by
    have hprod : {p : ι × X | IsLocalDiffeomorphAt I J r (f p.1) p.2} ∈
        l ×ˢ 𝓝ˢ K := by
      apply hK.mem_prod_nhdsSet_of_forall
      intro x hx
      obtain ⟨V, hV, hiV⟩ := hlocal x hx
      apply mem_of_superset (prod_mem_prod hiV hV)
      rintro ⟨i, y⟩ ⟨hi, hy⟩
      exact hi.1 ⟨y, hy⟩
    exact (Filter.Eventually.curry hprod).mono fun i hi x ↦
      hi.self_of_nhdsSet x (hSK x.property)
  apply eventually_exists_partialDiffeomorph_of_tendstoLocallyUniformlyOn_comp
    hK hS hSK f q r hregular _ hconv hg hinj
  intro x hx
  obtain ⟨V, hV, hiV⟩ := hlocal x hx
  exact ⟨V, nhdsWithin_le_nhds hV, hiV.mono fun _ hi ↦ hi.2⟩

end DifferentialGeometry.Topology.Manifold
