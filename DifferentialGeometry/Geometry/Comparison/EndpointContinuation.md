# EndpointContinuation

## Limit-based continuation API

`endpointCont_of_lim` contains the existing continuation argument with the endpoint
limit supplied explicitly, so it does not require ambient completeness.

The established `hasEndpointContinuation_of_complete` theorem is preserved as a
wrapper using the bounded-speed complete-space limit producer. `endpointCont_compact`
instead obtains the endpoint limit from eventual containment in a pseudo-emetric
compact set and reuses the same core theorem.

Focused verification and the named module refresh passed.
