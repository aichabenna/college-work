---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1680621144681201000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1680621144681202000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1680621144681203000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1680621144681204000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1680621144681205000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1680621144681208000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Tue Apr 04 17:12:24 CEST 2023 by ahamoir
