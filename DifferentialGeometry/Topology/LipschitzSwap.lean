import DifferentialGeometry.Topology.LocallyLipschitzOperations


open Filter Set
open scoped Topology

namespace LocallyLipschitzOn

variable {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
  [PseudoEMetricSpace Z]

theorem comp_swap {s : Set X} {t : Set Y} {f : X × Y → Z}
    (hf : LocallyLipschitzOn (s ×ˢ t) f) :
    LocallyLipschitzOn (t ×ˢ s) (fun p : Y × X => f (p.2, p.1)) := by
  have hswap : LocallyLipschitzOn (t ×ˢ s) (Prod.swap : Y × X → X × Y) :=
    (LipschitzWith.prod_snd.prodMk LipschitzWith.prod_fst).locallyLipschitz.locallyLipschitzOn
  exact hf.comp hswap (fun _ hp => ⟨hp.2, hp.1⟩)

end LocallyLipschitzOn
