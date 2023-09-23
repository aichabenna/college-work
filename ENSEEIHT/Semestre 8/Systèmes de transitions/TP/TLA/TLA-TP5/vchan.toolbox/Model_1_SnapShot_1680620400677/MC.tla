---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1680620397625168000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1680620397625169000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1680620397625170000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1680620397625171000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1680620397625172000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1680620397625175000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Tue Apr 04 16:59:57 CEST 2023 by ahamoir
