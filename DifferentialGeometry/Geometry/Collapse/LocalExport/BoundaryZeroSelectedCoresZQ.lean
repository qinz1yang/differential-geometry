import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroFaceParamOCX
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SelectedCoreOfSublevel74
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SelectedCoreOfCompactModel74

/-!
# The selected solid cores `Q` (Z1) of the boundary supply (lane S-ZQ, suffix `_ZQ`), group G1

The boundary full heads (`boundary_rows_of_actual_decomposition74_V32_OBD`,
`boundary_strongCertificate_V32_A4_OBD`, `member_separated_to_labelled_certificate_HB`, ...) take
the Z1 data
`Q : ∀ k : S.ZeroIdx_BAUGC, SelectedSmoothCore74 {q : W° | S.zeroRadial_BIFc k q ≤ 2 / 5}`
as an explicit input. It is NOT chain data: the sublevel `{radial_k ≤ 2/5}` is a sublevel of the
zero family of the supply's own family `S.family : LocalPacketsOnBFRZ`, whose field
`zero_sublevel_types` gives LPA05's five-way type clause for every `a ∈ [1/5, 2]`. The closed
side's five generic adapters (`nonempty_selectedCore74_of{PointSoul, CircleSoul, ProjectiveSoul,
KleinSoul, CompactModel}`, none of them needs compactness of the source) turn each case into a
selected smooth core, exactly as `LocalChartPacketsC14Z.nonempty_selectedCore74` does on the
closed family.

* `BoundarySupply.nonempty_selectedCore74_zero_ZQ S k`: `Nonempty (SelectedSmoothCore74 …)` for the
  zero index `k` (any `a ∈ [1/5, 2]` in the general form
  `BoundarySupply.nonempty_selectedCore74_zeroSublevel_ZQ`);
* `BoundarySupply.zeroSelectedCores_ZQ S`: the choice function, i.e. an inhabitant of the type of
  `Q`;
* `BoundarySupply.nonempty_zeroSelectedCores_ZQ S`: `Nonempty` of the type of `Q`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM)

/-- **Every actual zero sublevel `{radial_k ≤ a}`, `a ∈ [1/5, 2]`, of the supply is a selected
smooth core** (the boundary twin of `LocalChartPacketsC14Z.nonempty_selectedCore74`; the five
generic adapters of the closed side applied to `zero_sublevel_types` of `S.family`). -/
theorem nonempty_selectedCore74_zeroSublevel_ZQ (k : S.ZeroIdx_BAUGC) {a : ℝ}
    (ha : a ∈ Icc (1 / 5 : ℝ) 2) :
    Nonempty (SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ a}) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  rcases S.family.zero_sublevel_types k.1 ((Set.Finite.mem_toFinset _).mp k.2) a ha with
    h | h | h | h | h
  · exact nonempty_selectedCore74_ofCompactModel h
  · exact nonempty_selectedCore74_ofPointSoul h
  · exact nonempty_selectedCore74_ofCircleSoul h
  · exact nonempty_selectedCore74_ofProjectiveSoul h
  · exact nonempty_selectedCore74_ofKleinSoul h

/-- **The Z1 core of the zero index `k`** (`a = 2/5`): `Nonempty` of the type of one component of
`Q`. -/
theorem nonempty_selectedCore74_zero_ZQ (k : S.ZeroIdx_BAUGC) :
    Nonempty
      (SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ 2 / 5}) :=
  S.nonempty_selectedCore74_zeroSublevel_ZQ k ⟨by norm_num, by norm_num⟩

/-- **The selected solid cores `Q`** of the full boundary heads: an inhabitant of
`∀ k : S.ZeroIdx_BAUGC, SelectedSmoothCore74 {q | S.zeroRadial_BIFc k q ≤ 2 / 5}`, chosen from the
supply's own `zero_sublevel_types`. -/
def zeroSelectedCores_ZQ (k : S.ZeroIdx_BAUGC) :
    SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ 2 / 5} :=
  (S.nonempty_selectedCore74_zero_ZQ k).some

/-- `Nonempty` of the type of `Q`. -/
theorem nonempty_zeroSelectedCores_ZQ :
    Nonempty (∀ k : S.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ 2 / 5}) :=
  ⟨S.zeroSelectedCores_ZQ⟩

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse
