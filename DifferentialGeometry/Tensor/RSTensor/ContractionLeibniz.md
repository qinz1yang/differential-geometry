# ContractionLeibniz

## 2026-07-12 branch-alignment compatibility

The product Leibniz proof now unfolds the local field alias and evaluates through
`Bundle.continuousMultilinearMap.product_fun_apply`, avoiding failed rewriting through a section
coercion. Focused verification and targeted build passed. The product Leibniz theorem and its
dedicated machinery are complete (100%).
