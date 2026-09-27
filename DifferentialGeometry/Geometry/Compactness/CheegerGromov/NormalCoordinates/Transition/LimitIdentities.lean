import DifferentialGeometry.Geometry.Exponential.NormalBall.Chart
import DifferentialGeometry.Analysis.Calculus.MapConvergence.LimitIdentities

section

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

open scoped Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

theorem transition_comp {p q r : M}
    (c : NormalBallChart (I := I) p) (d : NormalBallChart (I := I) q)
    (e : NormalBallChart (I := I) r) {U : Set E}
    (hovl : c.OverlapOn d U) {z : E} (hz : z ∈ U) :
    d.transition e (c.transition d z) = c.transition e z := by
  change e.inv (d.hom (c.transition d z)) = e.inv (c.hom z)
  rw [hovl.map_eq hz]

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart


end

section

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

open Filter Topology
open scoped Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]

theorem transition_limit_comp
    {p q r : ∀ k, M k}
    (c : ∀ k, NormalBallChart (I := I) (p k))
    (d : ∀ k, NormalBallChart (I := I) (q k))
    (e : ∀ k, NormalBallChart (I := I) (r k))
    {U V : Set E} (hV : IsOpen V)
    {Jcd Jde Jce : E → E}
    (hcd : CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => (c k).transition (d k)) Jcd)
    (hde : CheegerGromovCompactness.MapCInfConvergenceOnCompacts V
      (fun k => (d k).transition (e k)) Jde)
    (hce : CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => (c k).transition (e k)) Jce)
    (hcont : ContinuousOn Jde V)
    (hovl : ∀ᶠ k in atTop, (c k).OverlapOn (d k) U)
    {z : E} (hz : z ∈ U) (hJcd : Jcd z ∈ V) :
    Jde (Jcd z) = Jce z := by
  apply CheegerGromovCompactness.comp_eq_of_mapCInfConvergenceOnCompacts_on
    hV hde hcont hcd hce ?_ hz hJcd
  filter_upwards [hovl] with k hk
  exact fun x hx => (c k).transition_comp (d k) (e k) hk hx

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart


end

section

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

open Filter
open scoped Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]

theorem eventually_not_disjoint_image_of_transition_limits
    {p q r : ∀ k, M k}
    (c : ∀ k, NormalBallChart (I := I) (p k))
    (d : ∀ k, NormalBallChart (I := I) (q k))
    (e : ∀ k, NormalBallChart (I := I) (r k))
    {U V A B : Set E} (hV : IsOpen V) (hB : IsOpen B)
    {Jcd Jde : E → E}
    (hcd : CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => (c k).transition (d k)) Jcd)
    (hde : CheegerGromovCompactness.MapCInfConvergenceOnCompacts V
      (fun k => (d k).transition (e k)) Jde)
    (hcont : ContinuousOn Jde V)
    (hovl : ∀ᶠ k in atTop, (c k).OverlapOn (d k) U)
    (hovl' : ∀ᶠ k in atTop, (d k).OverlapOn (e k) V)
    {z : E} (hz : z ∈ U) (hzA : z ∈ A)
    (hJcd : Jcd z ∈ V) (hcomp : Jde (Jcd z) ∈ B) :
    ∀ᶠ k in atTop, ¬ Disjoint ((c k).hom '' A) ((e k).hom '' B) := by
  have hlimcd := CheegerGromovCompactness.tendsto_of_cInf hcd hz
  have hlim := hde.tendsto_comp hV hlimcd hJcd (hcont _ hJcd)
  filter_upwards [hovl, hovl', hlimcd.eventually_mem (hV.mem_nhds hJcd),
    hlim.eventually_mem (hB.mem_nhds hcomp)] with k hk hk' hmem hcompmem
  intro hdisj
  apply hdisj.notMem_of_mem_left (Set.mem_image_of_mem (c k).hom hzA)
  refine ⟨(d k).transition (e k) ((c k).transition (d k) z), hcompmem, ?_⟩
  rw [hk'.map_eq hmem, hk.map_eq hz]

theorem near_of_composable_transition_limits
    {ι : Type*} (p : ι → ∀ k, M k)
    (c : ∀ i k, NormalBallChart (I := I) (p i k))
    (near : ι → ι → Bool) {U A : Set E} (hU : IsOpen U) (hA : IsOpen A)
    (hAU : A ⊆ U)
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => (c a.1.1 k).transition (c a.1.2 k)) (J a))
    (hcont : ∀ a, ContinuousOn (J a) U)
    (hovl : ∀ a : {a : ι × ι // near a.1 a.2 = true},
      ∀ᶠ k in atTop, (c a.1.1 k).OverlapOn (c a.1.2 k) U)
    (hfar : ∀ i j, near i j = false →
      ∀ᶠ k in atTop, Disjoint ((c i k).hom '' A) ((c j k).hom '' A))
    {i j l : ι} (hij : near i j = true) (hjl : near j l = true)
    {z : E} (hz : z ∈ A)
    (hJij : J ⟨(i, j), hij⟩ z ∈ U)
    (hJjl : J ⟨(j, l), hjl⟩ (J ⟨(i, j), hij⟩ z) ∈ A) :
    near i l = true := by
  have hn := eventually_not_disjoint_image_of_transition_limits
    (c i) (c j) (c l) hU hA (hconv ⟨(i, j), hij⟩) (hconv ⟨(j, l), hjl⟩)
    (hcont ⟨(j, l), hjl⟩) (hovl ⟨(i, j), hij⟩) (hovl ⟨(j, l), hjl⟩)
    (hAU hz) hz hJij hJjl
  cases h : near i l
  · have hfalse : ∀ᶠ k : ℕ in atTop, False := by
      filter_upwards [hn, hfar i l h] with k hk hk'
      exact hk hk'
    exact False.elim (Filter.Eventually.exists hfalse).choose_spec
  · rfl

theorem transition_limit_comp_of_near
    {ι : Type*} (p : ι → ∀ k, M k)
    (c : ∀ i k, NormalBallChart (I := I) (p i k))
    (near : ι → ι → Bool) {U : Set E} (hU : IsOpen U)
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => (c a.1.1 k).transition (c a.1.2 k)) (J a))
    (hcont : ∀ a, ContinuousOn (J a) U)
    (hovl : ∀ a : {a : ι × ι // near a.1 a.2 = true},
      ∀ᶠ k in atTop, (c a.1.1 k).OverlapOn (c a.1.2 k) U)
    {i j l : ι} (hij : near i j = true) (hjl : near j l = true)
    (hil : near i l = true) {z : E} (hz : z ∈ U)
    (hJij : J ⟨(i, j), hij⟩ z ∈ U) :
    J ⟨(j, l), hjl⟩ (J ⟨(i, j), hij⟩ z) = J ⟨(i, l), hil⟩ z := by
  exact transition_limit_comp (c i) (c j) (c l) hU
    (hconv ⟨(i, j), hij⟩) (hconv ⟨(j, l), hjl⟩) (hconv ⟨(i, l), hil⟩)
    (hcont ⟨(j, l), hjl⟩) (hovl ⟨(i, j), hij⟩) hz hJij

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart


end

section

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

open Filter
open scoped Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Nat → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]

theorem transition_limit_self
    {p : ∀ k, M k} (c : ∀ k, NormalBallChart (I := I) (p k))
    {U : Set E} {J : E → E}
    (hconv : CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => (c k).transition (c k)) J)
    (hsource : ∀ z ∈ U, ∀ᶠ k in atTop, z ∈ (c k).hom.source) :
    Set.EqOn J id U := by
  intro z hz
  apply tendsto_nhds_unique (CheegerGromovCompactness.tendsto_of_cInf hconv hz)
  apply tendsto_const_nhds.congr'
  filter_upwards [hsource z hz] with k hk
  exact ((c k).hom.left_inv hk).symm

theorem transition_limit_inverse_eq_reverse
    {ι : Type*} (p : ι → ∀ k, M k)
    (c : ∀ i k, NormalBallChart (I := I) (p i k))
    (near : ι → ι → Bool) (hsymm : ∀ i j, near i j = near j i)
    {U : Set E} {J Jbar : {a : ι × ι // near a.1 a.2 = true} → E → E}
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => (c a.1.1 k).transition (c a.1.2 k)) (J a))
    (hconvbar : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => (c a.1.2 k).transition (c a.1.1 k)) (Jbar a)) :
    ∀ i j (hij : near i j = true),
      Set.EqOn (Jbar ⟨(i,j),hij⟩) (J ⟨(j,i),hsymm i j ▸ hij⟩) U := by
  intro i j hij z hz
  exact (hconvbar ⟨(i,j),hij⟩).unique
    (hconv ⟨(j,i),hsymm i j ▸ hij⟩) ⟨hz,hz⟩

theorem transition_limit_cancel
    {p q : ∀ k, M k}
    (c : ∀ k, NormalBallChart (I := I) (p k))
    (d : ∀ k, NormalBallChart (I := I) (q k))
    {U V : Set E} (hV : IsOpen V) {J K : E → E}
    (hJ : CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => (c k).transition (d k)) J)
    (hK : CheegerGromovCompactness.MapCInfConvergenceOnCompacts V
      (fun k => (d k).transition (c k)) K)
    (hcont : ContinuousOn K V)
    (hovl : ∀ᶠ k in atTop, (c k).OverlapOn (d k) U)
    {z : E} (hz : z ∈ U) (hJz : J z ∈ V) : K (J z) = z := by
  have hlim := hK.tendsto_comp hV
    (CheegerGromovCompactness.tendsto_of_cInf hJ hz) hJz (hcont _ hJz)
  apply tendsto_nhds_unique hlim
  apply tendsto_const_nhds.congr'
  filter_upwards [hovl] with k hk
  exact ((c k).transition_cancel (d k) hk hz).symm

theorem transition_limit_invOn
    {p q : ∀ k, M k}
    (c : ∀ k, NormalBallChart (I := I) (p k))
    (d : ∀ k, NormalBallChart (I := I) (q k))
    {U V A B : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hAU : A ⊆ U) (hBV : B ⊆ V) {J K : E → E}
    (hJ : CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => (c k).transition (d k)) J)
    (hK : CheegerGromovCompactness.MapCInfConvergenceOnCompacts V
      (fun k => (d k).transition (c k)) K)
    (hcontJ : ContinuousOn J U) (hcontK : ContinuousOn K V)
    (hovl : ∀ᶠ k in atTop, (c k).OverlapOn (d k) U)
    (hovlrev : ∀ᶠ k in atTop, (d k).OverlapOn (c k) V) :
    Set.InvOn K J (A ∩ J ⁻¹' B) (B ∩ K ⁻¹' A) := by
  constructor
  · intro z hz
    exact transition_limit_cancel c d hV hJ hK hcontK hovl (hAU hz.1) (hBV hz.2)
  · intro z hz
    exact transition_limit_cancel d c hU hK hJ hcontJ hovlrev (hBV hz.1) (hAU hz.2)

theorem transition_limit_image_inter_preimage
    {p q : ∀ k, M k}
    (c : ∀ k, NormalBallChart (I := I) (p k))
    (d : ∀ k, NormalBallChart (I := I) (q k))
    {U V A B : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hAU : A ⊆ U) (hBV : B ⊆ V) {J K : E → E}
    (hJ : CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => (c k).transition (d k)) J)
    (hK : CheegerGromovCompactness.MapCInfConvergenceOnCompacts V
      (fun k => (d k).transition (c k)) K)
    (hcontJ : ContinuousOn J U) (hcontK : ContinuousOn K V)
    (hovl : ∀ᶠ k in atTop, (c k).OverlapOn (d k) U)
    (hovlrev : ∀ᶠ k in atTop, (d k).OverlapOn (c k) V) :
    J '' (A ∩ J ⁻¹' B) = B ∩ K ⁻¹' A := by
  have hinv := transition_limit_invOn c d hU hV hAU hBV
    hJ hK hcontJ hcontK hovl hovlrev
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz.2, by change K (J z) ∈ A; rw [hinv.1 hz]; exact hz.1⟩
  · intro hy
    refine ⟨K y, ⟨hy.2, ?_⟩, hinv.2 hy⟩
    change J (K y) ∈ B
    rw [hinv.2 hy]
    exact hy.1

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart


end
