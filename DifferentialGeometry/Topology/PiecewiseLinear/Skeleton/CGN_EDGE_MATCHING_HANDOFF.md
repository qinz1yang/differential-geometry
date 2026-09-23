# CGN edge matching — item 7 handoff

Owner: `codex-moise-recon`. Checkout: `D:\differential-geometry-moise-int`, branch `codex/moise-integration`.

## Status

The new `Section34EdgeMatchingLeaf.lean` compiles with zero diagnostics and exports the exact frozen `DifferentialGeometry.Topology.PiecewiseLinear.exists_section34EdgeMatching`. Its entire declaration through `:= by` and its complete `variable` block are byte-for-byte identical to `Skeleton/ControlledGraphNeighborhood.lean`.

Final audit status: **handed off at the owner's request**. The complete indexed audit reported no axiom errors and only two linter findings: the tool theorem's unused NormedSpace parameter and the frozen leaf's two SecondCountableTopology instances. Both source fixes are written. The subsequent 18-module dependency refresh and final repeat audit were stopped before completion, as requested.

The compiled pre-fix leaf had SHA-256 `31BD44CE1050A6C7BE1094DEB0C4B2B1A4237358A948C67527FF18961B112448`. Its mathematics is complete. Current proof-body and tool-signature cleanup needs the receiving lane's fresh checks. Use `cgn-linter-rebuild-order.txt` in the private output root, followed by `audit-cgn-edge-matching-final.lean`; do not assume every current source has a fresh receipt yet.

The frozen source remains SHA-256 `23CCC72F8D8296F0FF54EB3B122E1F786A02721A29D5F8BA3C28A0937D92568F`. No Git writes or root-aggregate edits were performed.

## Proof assembly

| Frozen clause | Real producer |
|---|---|
| (a), (b): PL vertex maps onto the deleted balls | `Section34JointCellMatching.lean`: `exists_section34_joint_cell_matching` |
| (c): pointwise agreement on every source intersection | The same producer, using the proved source adjacency theorem |
| (d): exact image intersections | The same producer, using the frozen target adjacency clause |
| (e): face rim is in the face-family interior | `FaceRimInteriorDeletedFamily.lean`: `face_rim_subset_interior_of_deleted_family` |
| (f): chart transport, nested tori, shell and exact spine | `Section34NestedDeletedTorus.lean`: `exists_nested_torus_of_deleted_family` |

The file labels in this table identify modules; the declarations live in `DifferentialGeometry.Topology.PiecewiseLinear`.

### Orientation argument

1. `InjectiveUnit`, `InjectiveCarrierSign`, `EmbeddingParity` and `ChartParity` prove unit local degree and constancy on the connected carriers.
2. `Section34RelativeVertexSigns` produces the vertex signs from the embedding, real reference ball maps, and the connected carriers. No closeness condition on the piercing maps is assumed.
3. `PLCellPairComparison` constructs the actual comparison `K = T₁ ∘ T₂⁻¹`, retaining each reference map on an entire source ball, and proves `K ∘ R₂ = R₁` on the shared disk.
4. `CellPairRelativeOrientation` computes its parity from the two vertex signs. `BallPairBoundaryOrientation` and `CellPairBoundaryOrientation` identify that parity with the actual disk-rim orientation, including the normal transfer and moving image basepoint.
5. `Section34RelativeEdgeCharacter` proves the actual disk discrepancy character is the endpoint coboundary. `GraphCoboundaryCycles` proves finite mod-two cycle cancellation, including loops and parallel edges.
6. `MarkedCellOrientation` constructs simultaneous vertex corrections. `Section34PositiveReferenceMaps` constructs the corrected reference maps and actual positive disk corrections in every covering chart.
7. `MarkedSpherePositiveExtension` supplies the outer circle correction while fixing the inner disks, applies `SphereHoledBoundaryExtension`, and glues full disks. `MarkedCellPositiveExtension` extends to the balls. `Section34JointCellMatching` then gives pointwise shared-disk agreement as an output.

### Torus argument

`Section34FaceVertexCycle` uses only subdivision, realization equality and endpoint data. `Section34DeletedFamilyTorus` applies `CyclicBallUnion` directly to the `Dv` family, proving nonadjacent disjointness and absence of triple intersections from the actual meeting disks. No `Section34GraphFrame` or homology generator premise is used.

`SpineNeighborhood` recenters the marked interior point of the given `IsSpine` product parametrisation and chooses one small radius uniformly over the compact circle. `RadialSolidTorusShell` uses the same radial parameter for the inner torus and shell and retains the exact spine. Thus the inner torus lies in `interior Te`; the generic shell-existence lemma is not used as a substitute for the spine clause.

## Integration

The lead can integrate the new leaf and its new dependencies after reviewing the receipts. The new real leaf and the frozen skeleton declare the same name: importing both simultaneously would duplicate that declaration. Replace the skeleton declaration during integration; the worker has left it unchanged under the new-files-only rule.

Register newly accepted modules in the flat root aggregate in the lead's integration pass. No whole-project build is claimed by this lane.

The checker and every per-module SHA-256 and sub-leaf list are recorded in `FILL_LOG.md`. Private artifacts and receipts are under `C:\Users\liao9\AppData\Local\Temp\codex-moise-recon`:

- `cgn-edge-matching-verified-modules.json`
- `audit-cgn-edge-matching-final.lean`
- `cgn-edge-matching-final-audit.json` after the final audit passes

Static scan of the 104 owned modules found no source proof placeholders, budget overrides, linter suppressions, exploratory commands, Skeleton imports, or trailing whitespace. Repository-wide `git diff --check` reports an unrelated pre-existing trailing space after `Manifest:` in the item 14 section of shared `FILL_LOG.md` (line 10370 at inspection); it was not edited under the append-only ownership rule.

## Exact verified source hashes

The table records the last fully verified pre-fix source set; the two current source hashes below supersede those rows and require the pending fresh checks. The manifest contains the absolute source and receipt paths. The table includes earlier accepted bricks owned by this lane as well as the new endpoint chain.

| Module | SHA-256 |
|---|---|
| `DifferentialGeometry.Topology.Combinatorics.GraphCoboundary` | `111AA1B8247ADCBC6D90F4CCD0C7146937E693D0901E3B462966E366DA8F32F3` |
| `DifferentialGeometry.Topology.Combinatorics.GraphCoboundaryCycles` | `A7197287A07980093634601B9385C83C115FF5E75591DCBAAAE8822D77B0C888` |
| `DifferentialGeometry.Topology.Compactness.LocallyFiniteClosedCover` | `6B0B29D9B99F199CC13D87CD5EB56E31A21802978F2C7B8D02FFB5EE06A24198` |
| `DifferentialGeometry.Topology.Homology.Local.OpenGenerator` | `B3669D8E8EC670427315B4E88D6662494DCD3DC82BFB2B5F9BF3EA651A750C0D` |
| `DifferentialGeometry.Topology.LocalDegree.BoundarySphereDegree` | `D86FE9628889C6D88ED8610BA48964F8BC34FBF47419D341B1B998041EF8282B` |
| `DifferentialGeometry.Topology.LocalDegree.BoundaryTraceOrientation` | `10AEE0DB6C099B36FB7B756F044B3C989A786B2408FBEB5714F999251FD81A83` |
| `DifferentialGeometry.Topology.LocalDegree.BoundaryTraceOrientationAt` | `D70634C68436B79C9073B64B9215EA8342E7486A7F8914F81A9CBC877D1A4C57` |
| `DifferentialGeometry.Topology.LocalDegree.ChartComparison` | `D4245BBB78894EE5D2D6E2622A6CBB7ABDF69F2EF288854B3AA90B120766D29F` |
| `DifferentialGeometry.Topology.LocalDegree.ChartGraphCharacter` | `BAADFA647CEAD8C1B7F147465BAC192D4B855C1988A34DA1748A468A8F65B307` |
| `DifferentialGeometry.Topology.LocalDegree.ChartParity` | `54CDF48A18B2B87DDD0ACACA1DE6CDB488E084D6CD8A594E090D4B8456D8DA98` |
| `DifferentialGeometry.Topology.LocalDegree.ChartParityGerm` | `43B3BA02BAC3870F6AC832F30361ABF15E4AE8138283311D46DE7A41D98F69C1` |
| `DifferentialGeometry.Topology.LocalDegree.ChartParityTransport` | `29A81D2E2A3DC3EAFD002C2AE19F65F7F2DDC843609981D621F11AA905750B59` |
| `DifferentialGeometry.Topology.LocalDegree.CompactSupportOrientation` | `59644A04C906E60AB669BF658385408B34CDFDC632A0A641FB6BC94DEDCE7E5F` |
| `DifferentialGeometry.Topology.LocalDegree.EmbeddingComposition` | `C2E3939918E49617C6593A3F3F36F505CEB3CBC29D00ACC44B1F431DCD1FD4D2` |
| `DifferentialGeometry.Topology.LocalDegree.EmbeddingParity` | `FDBEB177DCC96207CE4505231B2A2462734F9B10E774EAEA7032CED214F76AF1` |
| `DifferentialGeometry.Topology.LocalDegree.EmbeddingTranslation` | `DAA5CA27A2D76EA14B7D74771A963F6E6E331E51349866EAA4B71B2E94D96C2B` |
| `DifferentialGeometry.Topology.LocalDegree.HalfSpace` | `7DC3103F879D0AA9E75576CC25D1A308D1F3D51B02F6043EBDA48E19F0CDF13F` |
| `DifferentialGeometry.Topology.LocalDegree.HalfSpaceOpen` | `94C1AF6591054776778038B8D76D84F3673C7B86AE5D3ECCCD0D2333EA88AAC7` |
| `DifferentialGeometry.Topology.LocalDegree.HomeomorphConjugation` | `91FDB7EB64D03F574FCBCACA7DB07014D31DA7AD317E284CF83298CA55652DE5` |
| `DifferentialGeometry.Topology.LocalDegree.HyperplaneTrace` | `DAB76E4ACB34FF852E9035325180A6D34866D0668E793DCEEFD9E4AEE98025FD` |
| `DifferentialGeometry.Topology.LocalDegree.InjectiveCarrierSign` | `4143EB0141C5F123B227D7A7866D1B818413612AD7A5CD9C00CA9A6908154F40` |
| `DifferentialGeometry.Topology.LocalDegree.InjectiveOrientationCharacter` | `C635CE483C783565514AE83123DAF73488D2647A5DEADFCA84481572809F4DF5` |
| `DifferentialGeometry.Topology.LocalDegree.InjectiveRelativeIso` | `4E6CDFE01729D44046016C390D65E43572F018D189A47620911D156776D57128` |
| `DifferentialGeometry.Topology.LocalDegree.InjectiveUnit` | `BFB40CC4B45EB10882D95119A8376683891F49008B93A80CE1FD66F3BE159E27` |
| `DifferentialGeometry.Topology.LocalDegree.OpenDomain` | `C784BF9FC6198C87F7C6D0FB9AA85C585ACEED2F951B4B7CD83313860AE04F78` |
| `DifferentialGeometry.Topology.Manifold.BoundaryNormalParity` | `F81E17F1A9B05F99759869BB2838A2F687BD81183FEE747F2A1A5347C1348AE0` |
| `DifferentialGeometry.Topology.Manifold.BoundaryNormalSignTransfer` | `10AFEDA4BB1531C081CDB8600A122CB5F90E1C1901CFD723660B105A44EA0CA9` |
| `DifferentialGeometry.Topology.Manifold.EmbeddingLocalHomeomorph` | `BF74D4DF0A5FF0E8296B4C1FFAF7D4E7F71B305700651989F8987D77706EA507` |
| `DifferentialGeometry.Topology.PiecewiseLinear.BallComplementFamily` | `9F7EA14D0C06244461DFC7677FA22C2501C624F0837B79549C0B8505CD122565` |
| `DifferentialGeometry.Topology.PiecewiseLinear.BallPairBoundaryOrientation` | `3457EFCCF20BABAF893851874948BF49DEF40A803017A13EC92FA63537834234` |
| `DifferentialGeometry.Topology.PiecewiseLinear.BallPairHalfSpaceChart` | `A33473CF462B8FAE4A6F7C052154F79CA96D43613CFE6BD5A6BD7F54853F5312` |
| `DifferentialGeometry.Topology.PiecewiseLinear.BoundaryCollarExtension` | `4EBBFDD71FB5CC36E7782EF8237557EF3C8140CBCFF307EF017FB44DDB74CC2D` |
| `DifferentialGeometry.Topology.PiecewiseLinear.CellDiskOrientationCorrection` | `2C91E1FC0625E846D3B72FF12EECD6939D77F7B4B6F6ABF232799EC0DA74B8E7` |
| `DifferentialGeometry.Topology.PiecewiseLinear.CellPairBoundaryOrientation` | `94B5F35C2F774F2B3687CF6F6EA41D676F0AF2F974E5A588B8097443E35B1D1B` |
| `DifferentialGeometry.Topology.PiecewiseLinear.CellPairRelativeOrientation` | `8661385AAF7FF3A26323238D49D30C2AD435C6C5E0854DCDD826AB7C2873C990` |
| `DifferentialGeometry.Topology.PiecewiseLinear.ChartCircleOrientation` | `E5178DB3F29B73A109392D528CE806B1D6FDCA1E0B1D1CF771211CE8D126F96C` |
| `DifferentialGeometry.Topology.PiecewiseLinear.CircleDegreeOrientation` | `7BB97EA19B8F8798F86F9080253CE571E63F9539E116D1F3EC88ACFE74962D0C` |
| `DifferentialGeometry.Topology.PiecewiseLinear.CircleLocalDegreeOrientation` | `A910FDACA961913AB57E59E00399DF0821A30E55842E1DD0DEF7FF65D62ED58C` |
| `DifferentialGeometry.Topology.PiecewiseLinear.CircleOrientationParity` | `85317A25D61E84C7DA79FC2670B8EC1D41602E4E820DC9C7013F1215EC189B9E` |
| `DifferentialGeometry.Topology.PiecewiseLinear.CirclePositiveConjugation` | `91959F6049B29948DD8DAC883F0BA2C8C9FE0A4CC2B4CB82DA4E8971930F3F2B` |
| `DifferentialGeometry.Topology.PiecewiseLinear.CyclicBallUnion` | `398402A484516B31431D12564C51A8435FB827D053E7415F4B56B36606A481E2` |
| `DifferentialGeometry.Topology.PiecewiseLinear.DiskLocalDegreeOrientation` | `EF10B194E9A2225A6911767DD8BA6BA09CB2C573D5DF51A06132761B4D1AF1EA` |
| `DifferentialGeometry.Topology.PiecewiseLinear.FaceRimInteriorDeletedFamily` | `706080191302970488215C1625D702279211DBE2CF5651ED86C9BF76AA5853E9` |
| `DifferentialGeometry.Topology.PiecewiseLinear.HalfSpaceCircleOrientation` | `7814537D04FFE29282A1D0257DB9DD7B6FF938542C4B9B9324C0C59E6EA14E15` |
| `DifferentialGeometry.Topology.PiecewiseLinear.HoledDiskBoundaryExtension` | `071C89CACAE7FF82A753A8FF24E81916B6ACDDF288A309F3FED8BC4035905AA3` |
| `DifferentialGeometry.Topology.PiecewiseLinear.HoledSphereClosed` | `6C5E5889D60BA48EFFD9AB0AEC9A8FED90170D9BED19D97FC7D32A698A4EAB81` |
| `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteManifoldCofaces` | `737545070FC6D62D0A38687C304605A21E6C16EE213DCA59DFF6FD8308216764` |
| `DifferentialGeometry.Topology.PiecewiseLinear.MarkedCellOrientation` | `D9FC6A3D8E996E80691AC9B446F4D5FDE25659197573E0DFE72D885455115BC1` |
| `DifferentialGeometry.Topology.PiecewiseLinear.MarkedCellPositiveExtension` | `C7B8562C4A0E46B5899B66D2548C46110294AAEADED6E2F13A30686BEEEDB805` |
| `DifferentialGeometry.Topology.PiecewiseLinear.MarkedSphereBoundaryExtension` | `4F1A108579DAB921501DA622F3132D1207330DFC4AF787E5BE9B830609C55B8C` |
| `DifferentialGeometry.Topology.PiecewiseLinear.MarkedSphereFamilyMap` | `E740166C2A83C60BEEA435CCCC5628E5C8D01A1A8E33DDBFE3EC19B962377CDD` |
| `DifferentialGeometry.Topology.PiecewiseLinear.MarkedSphereOrientation` | `766190A2A2B078225B81013BC9CD5FAEED18585714A86F1133607E7BE7AEDF34` |
| `DifferentialGeometry.Topology.PiecewiseLinear.MarkedSpherePositiveExtension` | `D274B8300350372CB36A2E1262867A4DAF25E77D2088947524BD22CBCBCF7267` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PlanarBoundaryCollars` | `353C4456B4681DE621C318BBB6B0B35AC7C2D42EBEC0AAA3A3E23CA9EC23B436` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskFamilyMove` | `F8E2905CAD14CD18DAC79BB2F6ABAD4786231589DEC096C8E71604756F8127DE` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskOrientation` | `ECD7228115E1AEF1DE8FB8E0634EA4AE6CB5A7C47BFFB6A431B15B8F4B7ED0B6` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PlanarHoledCollars` | `AF67495708399D19652B4B2D758BC3D2A21047041A1E881FEC8051200A9C81A6` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PlanarOuterCollar` | `F56D7F7C39AD77D40FF42E757103BB1125CBE25C710D1CB610DCC8B45282BFE5` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PlanarSubdiskOrientation` | `DA912F6B0C7F063776CE265C755750013B63001AE94C183FA768B3D02097C48A` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PLBallPairCenteredPrism` | `5B2B7836FA92494A71638D91BA3B0A7E2ED577020F0F43B05EFE1C9A47953DE1` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PLBallPairNormalForm` | `12121AA3AC53405DE7269674C94368E3573EF04A29EC519213ABF3F182B66D3D` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PLCellBoundaryHoledChart` | `10FC5D3923377A0C138428D4EDEF9122FE554950E9C02495326FE80B372DBFBD` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PLCellBoundaryMarkedMap` | `776770A722370EC25CA2BC26AF21043CDBABB4F32F3FC748BD1E489BC1A92388` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PLCellDiskExtension` | `F27140D0F4AE2FF3441452E0F335CD4F2B4A517089A6CB58EA052A2A4BDE3414` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PLCellInteriorImage` | `048C376FA85C08EBE7766E92CECBCC39EDBBDA4F5388AF257273D034FB665FBE` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PLCellMapInterior` | `04E3E04DAB3247A64EFC601FE8C3DF3C30516451F53D4CCD253480C005FABDBB` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PLCellPairCenteredPrism` | `CA4274BC6B492DCB54FC597E79AA0F89C25D58E70874C1B40C2920C895BB8271` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PLCellPairComparison` | `E1EE03AC59D074FB689FDA5B0600BA9C769310CB9F5B4E7F768826453E241ACA` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PLCellPairExtension` | `48385339B121BDBD9F5189771D572BC86960C95E781BA7800DC495196D7BC005` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PLCellPairHalfSpaceChart` | `1DB08202199FECF7D54694E8A07F2FEE57E8DBC80565BB84BE39E701B227E587` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PLCellPairMap` | `E63E1DBCB51FCBC03A95FB4D915FE260357F026A1395A647764497457C1CC0F5` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PLCellPullback` | `4076669D7D5A37E73B6CBE6B42CDF560F5068BA6591FBB9F0E448CEBD9D3C0EF` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PLCellRelativeOrientation` | `C2526803DC55DF0C458B211EB7EE48898FAC5889A8A8CF45F40D22513751F06D` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphIntoInverse` | `1B20258C21C1EF7B8AC14C3E2622DB6C04E6BD9AD233DD8407F75892052C2E2E` |
| `DifferentialGeometry.Topology.PiecewiseLinear.PositiveBoundaryExtension` | `71BCA0D5D1E9D770203375ECCA8BE4AE78E2763AFA5A5A3DF570915B6EFD73FD` |
| `DifferentialGeometry.Topology.PiecewiseLinear.RadialSolidTorusShell` | `0D08B5C38FAAB63D12E938605A6930B81ADE274508171DF98237251D2263A388` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34BoundaryDiskFamilies` | `F68F282F9D244873E2F33C57A38CCEED1D860DE885C23D791EF001BDDFC5E537` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34CarrierOrientation` | `7F2F66AEA64F2656FA63EF333D63D0614045F3ADC05730FA6AFAF45DB6967A36` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary` | `45FCD951D1A4EBA0C27604BD13DC4B5FAD18966E8EE01C3F2F1D1EE108C633BD` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34ConnectedCarriers` | `6DA1E6301427DDD47CE770F4608066F993C2A9D9598F828D7A5441DAF08324D6` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34DeletedFamilyTorus` | `B337DE144F4964D6DCA1BB8EF55BBF12318CE1A11A0BC8B8C0FE9B248764CCB8` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34EdgeCommonChart` | `EC82B8AAE49BC32CBE3985813EDF8A1A0E95C5729ECB705EAA4796F0776BDFF0` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34EdgeMatchingLeaf` | `31BD44CE1050A6C7BE1094DEB0C4B2B1A4237358A948C67527FF18961B112448` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34EdgeTargetPrism` | `465F78788ADC76B4AF1FD1A085A917A70E85615D7B6853E7D762000CDC387BE2` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceVertexCycle` | `0655C698E1F65A1F737915549D4385421AD21CF0EE870631580C62369105DFA0` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdgeFinite` | `F3C459B71AEF41D1B649A84B1BEB841E5657170DE98E54F8D6F355BC7CE658C3` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34JointCellMatching` | `B27E7965BFCE33D61A717347BF2B50542E0E264CA1FACAA627AB6DD56446C04B` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34NestedDeletedTorus` | `0B753E2A23D7BC8490CDA4DBF8D710FAA7023EC7EBF0D0DFF039432C89AAFE1A` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34PositiveReferenceMaps` | `93DB4485251538081765F7D82CCCF3E1D81B98AFA9AFB9DA3273459E4B13C344` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34ReferenceBallMaps` | `4D9F32FA1B5FB49C40EC2A73A7A3B40D713CC765EC426DD3C85A8D157CD7F44F` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34ReferenceSphereMaps` | `9D413889B5A32A4CF908C54D63A0B3D1D6B419B0DA5B66A66E5CE1DE71F3297A` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34RelativeEdgeCharacter` | `E81C401B0D475C7234B9781D54E3F0A4E5D56D5407967FB13A1F0B2E34E14AA0` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34RelativeVertexSigns` | `552E62D80C97CB4C6C98FDF2DE911D1DBDBB54C0933D019B467D637165FA999E` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34SourceVertexAdjacency` | `C873BE8EF0A62B5CC54915939845FE7727CA328C490BB85A51EEB72CC31A8B9B` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34SplitDisksDisjoint` | `1F032CD2B4BB073F8022F8BA7BE691ACA803C3A3AD37A923348EB96682C3FD98` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexIncidentEdge` | `67415F433FBEE6EC639964B134F34961CDE561A5CE44CB06D2D1951B7DE7FD94` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexInteriorOverlap` | `7F23553F1A9111A0FA89CAD02030B39B266763355B62822EF1552B98D5AAFB22` |
| `DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexMarkerInterior` | `7D5E2FFE55C3EE027DA76503D441DC55B1DB9CFA29F1E9F82D68E170CEAC6A71` |
| `DifferentialGeometry.Topology.PiecewiseLinear.SphereHoledBoundaryExtension` | `59EF30F80DE9B86880212474B44D9A53482449B1BBBD3138CBA3D9654A51A49B` |
| `DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskTraceChart` | `BC925997E1DBFC724241789E7F45C7FA274771E8A9AA28D1A07316CECCBE1395` |
| `DifferentialGeometry.Topology.PiecewiseLinear.SpineNeighborhood` | `20A89F71B0779F3AD78384636D3DE3C3E9E6D347ADA985F64749B6EBB86042B4` |
| `DifferentialGeometry.Topology.PiecewiseLinear.SplittingDiskRim` | `8F40CA13EDCBC06BBD971C9380A52BD0B76351982CCE542B1F323F3EC8011B04` |
| `DifferentialGeometry.Topology.PiecewiseLinear.TorusCircleHomology` | `C0BD2676246511D7EA52728163E89C7222380A12872F033B462CE1C3A32C82A9` |
| `DifferentialGeometry.Topology.PiecewiseLinear.TubeOfGraphDualCells` | `FD1E2719086E38F578E5DC0C23D0EA4AE597E0CBDAE9B4514286BBE4EED6F500` |

## Current source fixes pending receiver verification

- `Section34EdgeMatchingLeaf.lean`: `E5E6FA5F9FD8FD87381DC69D089DCCCF21CFA9C8B1D4800CFA6A02B894DDF9CE`
- `CircleDegreeOrientation.lean`: `209F4B66B8673D1F766B3C4F7722CCF7E172AFE41F764DE58051F6C66043D132`
